import psycopg
from decimal import Decimal
import math

def test_psycopg_extended_mode():
    conn = psycopg.connect(host='localhost', port='4566', dbname='dev', user='root')
    # conn = psycopg.connect(host='localhost', port='5432', dbname='test', user='eric')
    with conn.cursor() as cur:
        # Array
        cur.execute("select Array[1::bigint, 2::bigint, 3::bigint]", binary=True)
        assert cur.fetchone() == ([1, 2, 3],)

        cur.execute("select Array['foo', null, 'bar']", binary=True)
        assert cur.fetchone() == (['foo', None, 'bar'],)

        # Struct
        cur.execute("select ROW('123 Main St'::varchar, 'New York'::varchar, 10001)", binary=True)
        assert cur.fetchone() == (('123 Main St', 'New York', 10001),)

        cur.execute("select array[ROW('123 Main St'::varchar, 'New York'::varchar, 10001), ROW('234 Main St'::varchar, null, 10002)]", binary=True)
        assert cur.fetchone() == ([('123 Main St', 'New York', 10001), ('234 Main St', None, 10002)],)

        # Numeric
        cur.execute("select 'NaN'::numeric, 'NaN'::real, 'NaN'::double precision", binary=True)
        result = cur.fetchone()
        assert result[0].is_nan()
        assert math.isnan(result[1])
        assert math.isnan(result[2])

        cur.execute("select 'Infinity'::numeric, 'Infinity'::real, 'Infinity'::double precision")
        assert cur.fetchone() == (float('inf'), float('inf'), float('inf'))

        cur.execute("select '-Infinity'::numeric, '-Infinity'::real, '-Infinity'::double precision")
        assert cur.fetchone() == (float('-inf'), float('-inf'), float('-inf'))

if __name__ == '__main__':
    test_psycopg_extended_mode()
