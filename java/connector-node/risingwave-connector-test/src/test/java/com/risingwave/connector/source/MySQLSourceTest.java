// Copyright 2023 RisingWave Labs
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package com.risingwave.connector.source;

import static org.assertj.core.api.Assertions.*;
import static org.junit.Assert.assertEquals;

import com.risingwave.connector.ConnectorServiceImpl;
import com.risingwave.proto.ConnectorServiceProto;
import com.risingwave.proto.ConnectorServiceProto.*;
import com.risingwave.proto.Data;
import io.grpc.*;
import java.io.IOException;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.*;
import javax.sql.DataSource;
import org.junit.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.testcontainers.containers.MySQLContainer;
import org.testcontainers.utility.MountableFile;

public class MySQLSourceTest {

    static final Logger LOG = LoggerFactory.getLogger(MySQLSourceTest.class.getName());

    private static final MySQLContainer<?> mysql =
            new MySQLContainer<>("mysql:8.0")
                    .withDatabaseName("test")
                    .withUsername("root")
                    .withCopyFileToContainer(
                            MountableFile.forClasspathResource("my.cnf"), "/etc/my.cnf");

    public static Server connectorServer =
            ServerBuilder.forPort(SourceTestClient.DEFAULT_PORT)
                    .addService(new ConnectorServiceImpl())
                    .build();

    public static SourceTestClient testClient =
            new SourceTestClient(
                    Grpc.newChannelBuilder(
                                    "localhost:" + SourceTestClient.DEFAULT_PORT,
                                    InsecureChannelCredentials.create())
                            .build());

    private static DataSource mysqlDataSource;

    @BeforeClass
    public static void init() {
        // generate orders.tbl test data
        SourceTestClient.genOrdersTable(10000);
        // start connector server and mysql...
        try {
            connectorServer.start();
            LOG.info("connector service started");
            mysql.withCopyFileToContainer(
                    MountableFile.forClasspathResource("orders.tbl"), "/home/orders.tbl");
            mysql.start();
            mysqlDataSource =
                    SourceTestClient.getDataSource(
                            mysql.getJdbcUrl(),
                            mysql.getUsername(),
                            mysql.getPassword(),
                            mysql.getDriverClassName());
            LOG.info("mysql started");
        } catch (IOException e) {
            fail("IO exception: ", e);
        }
        // check mysql configuration...
        try {
            Connection connection = SourceTestClient.connect(mysqlDataSource);
            ResultSet resultSet =
                    SourceTestClient.performQuery(
                            connection, testClient.sqlStmts.getProperty("mysql.bin_log"));
            assertThat(resultSet.getString("Value")).isEqualTo("ON").as("MySQL: bin_log ON");
            connection.close();
        } catch (SQLException e) {
            fail("SQL exception: ", e);
        }
    }

    @AfterClass
    public static void cleanup() {
        connectorServer.shutdown();
        mysql.stop();
    }

    // create a TPC-H orders table in mysql
    // insert 10,000 rows into orders
    // check if the number of changes debezium captures is 10,000
    @Test
    public void testLines() throws InterruptedException, SQLException {
        ExecutorService executorService = Executors.newFixedThreadPool(1);
        Connection connection = SourceTestClient.connect(mysqlDataSource);
        String query = testClient.sqlStmts.getProperty("tpch.create.orders");
        SourceTestClient.performQuery(connection, query);
        query =
                "LOAD DATA INFILE '/home/orders.tbl' "
                        + "INTO TABLE orders "
                        + "CHARACTER SET UTF8 "
                        + "FIELDS TERMINATED BY '|' LINES TERMINATED BY '\n';";
        SourceTestClient.performQuery(connection, query);
        Iterator<GetEventStreamResponse> eventStream =
                testClient.getEventStreamStart(mysql, SourceType.MYSQL, "test", "orders");
        Callable<Integer> countTask =
                () -> {
                    int count = 0;
                    while (eventStream.hasNext()) {
                        List<CdcMessage> messages = eventStream.next().getEventsList();
                        for (CdcMessage ignored : messages) {
                            count++;
                        }
                        if (count == 10000) {
                            return count;
                        }
                    }
                    return count;
                };
        Future<Integer> countResult = executorService.submit(countTask);
        try {
            int count = countResult.get();
            LOG.info("number of cdc messages received: {}", count);
            assertEquals(10000, count);
        } catch (ExecutionException e) {
            fail("Execution exception: ", e);
        } finally {
            // cleanup
            query = testClient.sqlStmts.getProperty("tpch.drop.orders");
            SourceTestClient.performQuery(connection, query);
            connection.close();
        }
    }

    // test whether validation catches permission errors
    @Test
    public void testPermissionCheck() throws SQLException {
        // user Root creates a superuser debezium
        Connection connRoot = SourceTestClient.connect(mysqlDataSource);
        String query = "CREATE USER debezium IDENTIFIED BY '" + mysql.getPassword() + "'";
        SourceTestClient.performQuery(connRoot, query);
        query =
                "GRANT SELECT, RELOAD, SHOW DATABASES, REPLICATION SLAVE, REPLICATION CLIENT ON *.* TO 'debezium'";
        SourceTestClient.performQuery(connRoot, query);
        query =
                "CREATE TABLE IF NOT EXISTS orders (o_key BIGINT NOT NULL, o_val INT, PRIMARY KEY (o_key))";
        SourceTestClient.performQuery(connRoot, query);
        ConnectorServiceProto.TableSchema tableSchema =
                ConnectorServiceProto.TableSchema.newBuilder()
                        .addColumns(
                                ConnectorServiceProto.TableSchema.Column.newBuilder()
                                        .setName("o_key")
                                        .setDataType(Data.DataType.TypeName.INT64)
                                        .build())
                        .addColumns(
                                ConnectorServiceProto.TableSchema.Column.newBuilder()
                                        .setName("o_val")
                                        .setDataType(Data.DataType.TypeName.INT32)
                                        .build())
                        .addPkIndices(0)
                        .build();

        try {
            var resp =
                    testClient.validateSource(
                            mysql.getJdbcUrl(),
                            mysql.getHost(),
                            "debezium",
                            mysql.getPassword(),
                            SourceType.MYSQL,
                            tableSchema,
                            "test",
                            "orders");
            assertEquals(
                    "INVALID_ARGUMENT: MySQL user does not have privilege LOCK TABLES, which is needed for debezium connector",
                    resp.getError().getErrorMessage());
        } catch (Exception e) {
            Assert.fail("validate rpc fail: " + e.getMessage());
        } finally {
            // cleanup
            query = testClient.sqlStmts.getProperty("tpch.drop.orders");
            SourceTestClient.performQuery(connRoot, query);
            query = "DROP USER IF EXISTS debezium";
            SourceTestClient.performQuery(connRoot, query);
            connRoot.close();
        }
    }

    // generates test cases for the risingwave debezium parser
    @Ignore
    @Test
    public void getTestJson() throws InterruptedException, SQLException, ExecutionException {
        try (Connection connection = SourceTestClient.connect(mysqlDataSource)) {
            ExecutorService executorService = Executors.newFixedThreadPool(1);
            String query =
                    "CREATE TABLE IF NOT EXISTS orders ("
                            + "O_KEY BIGINT NOT NULL, "
                            + "O_BOOL BOOLEAN, "
                            + "O_TINY TINYINT, "
                            + "O_INT INT, "
                            + "O_REAL REAL, "
                            + "O_DOUBLE DOUBLE, "
                            + "O_DECIMAL DECIMAL(15, 2), "
                            + "O_CHAR CHAR(15), "
                            + "O_DATE DATE, "
                            + "O_TIME TIME, "
                            + "O_DATETIME DATETIME, "
                            + "O_TIMESTAMP TIMESTAMP, "
                            + "O_JSON JSON, "
                            + "PRIMARY KEY (O_KEY))";
            SourceTestClient.performQuery(connection, query);
            Iterator<GetEventStreamResponse> eventStream =
                    testClient.getEventStreamStart(mysql, SourceType.MYSQL, "test", "orders");
            Callable<Void> getCdcMsgTask =
                    () -> {
                        int i = 0;
                        if (eventStream.hasNext()) {
                            List<CdcMessage> messages = eventStream.next().getEventsList();
                            for (CdcMessage msg : messages) {
                                System.out.printf("CDC Message %d:\n%s\n", i, msg.getPayload());
                                i++;
                            }
                        }
                        return null;
                    };
            Future<Void> printResult = executorService.submit(getCdcMsgTask);
            Thread.sleep(3000);
            // Q1: ordinary insert
            query =
                    "INSERT INTO orders (O_KEY, O_BOOL, O_TINY, O_INT, O_REAL, O_DOUBLE, O_DECIMAL, O_CHAR, O_DATE, O_TIME, O_DATETIME, O_TIMESTAMP, O_JSON)"
                            + "VALUES(111, TRUE, -1, -1111, -11.11, -111.11111, -111.11, 'yes please', '1000-01-01', '00:00:00', '1970-01-01 00:00:00', '1970-01-01 00:00:01.000000', '{\"k1\": \"v1\", \"k2\": 11}')";
            SourceTestClient.performQuery(connection, query);
            // Q2: update value of Q1 (value -> new value)
            query =
                    "UPDATE orders SET O_BOOL = FALSE, "
                            + "O_TINY = 3, "
                            + "O_INT = 3333, "
                            + "O_REAL = 33.33, "
                            + "O_DOUBLE = 333.33333, "
                            + "O_DECIMAL = 333.33, "
                            + "O_CHAR = 'no thanks', "
                            + "O_DATE = '9999-12-31', "
                            + "O_TIME = '23:59:59', "
                            + "O_DATETIME = '5138-11-16 09:46:39', "
                            + "O_TIMESTAMP = '2038-01-09 03:14:07', "
                            + "O_JSON = '{\"k1\": \"v1_updated\", \"k2\": 33}' "
                            + "WHERE orders.O_KEY = 111";
            SourceTestClient.performQuery(connection, query);
            // Q3: delete value from Q1
            query = "DELETE FROM orders WHERE orders.O_KEY = 111";
            SourceTestClient.performQuery(connection, query);
            printResult.get();
        }
    }

    @Ignore
    @Test
    public void getTestJsonTypeTest()
            throws InterruptedException, SQLException, ExecutionException {
        try (Connection connection = SourceTestClient.connect(mysqlDataSource)) {
            String query =
                    "CREATE TABLE orders("
                            + "o_key integer,"
                            + "o_bit bit,"
                            + "o_float float,"
                            + "o_float_6_3 float(6, 3),"
                            + "o_varchar varchar(3),"
                            + "o_binary binary,"
                            + "o_varbinary varbinary(3),"
                            + "o_blob blob,"
                            + "o_text text,"
                            + "o_enum enum('polar', 'brown', 'panda'),"
                            + "o_year year,"
                            + "o_datetime_0 datetime(0),"
                            + "o_datetime_6 datetime(6),"
                            + "o_decimal decimal(4,3),"
                            + "PRIMARY KEY (o_key))";
            SourceTestClient.performQuery(connection, query);
            Iterator<GetEventStreamResponse> eventStream =
                    testClient.getEventStreamStart(mysql, SourceType.MYSQL, "test", "orders");
            query =
                    "insert into orders values (1, b'1', 2.222, 333.333, 'hhh', 0xaa, 0xabcdef, 0xbb, 'haha', 'polar', 2023, '2023-05-23 16:16:16', '2023-05-23 16:16:16.123456', 2.222);";
            SourceTestClient.performQuery(connection, query);
            if (eventStream.hasNext()) {
                List<CdcMessage> messages = eventStream.next().getEventsList();
                for (CdcMessage msg : messages) {
                    System.out.printf("%s\n", msg.getPayload());
                }
            }
        }
    }
}
