package com.risingwave.planner.rel.logical;

import com.google.common.collect.ImmutableList;
import com.risingwave.catalog.ColumnCatalog;
import com.risingwave.catalog.TableCatalog;
import com.risingwave.planner.rel.common.FilterScanBase;
import java.util.List;
import org.apache.calcite.plan.Convention;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelOptCost;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptTable;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.convert.ConverterRule;
import org.apache.calcite.rel.hint.RelHint;
import org.apache.calcite.rel.logical.LogicalTableScan;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.checkerframework.checker.nullness.qual.Nullable;

public class RwLogicalFilterScan extends FilterScanBase implements RisingWaveLogicalRel {

  private RwLogicalFilterScan(
      RelOptCluster cluster,
      RelTraitSet traitSet,
      List<RelHint> hints,
      RelOptTable table,
      TableCatalog.TableId tableId,
      ImmutableList<ColumnCatalog.ColumnId> columnIds,
      boolean stream) {
    super(cluster, traitSet, hints, table, tableId, columnIds, stream);
    checkConvention();
  }

  public RwLogicalFilterScan copy(ImmutableList<ColumnCatalog.ColumnId> columnIds) {
    return new RwLogicalFilterScan(
        getCluster(), getTraitSet(), getHints(), getTable(), tableId, columnIds, isStream());
  }

  @Override
  public @Nullable RelOptCost computeSelfCost(RelOptPlanner planner, RelMetadataQuery mq) {
    double valueCount = table.getRowCount() * columnIds.size();
    double cpu = valueCount + 1;
    double io = 0;
    return planner.getCostFactory().makeCost(valueCount, cpu, io);
  }

  public static class RwLogicalFilterScanConverterRule extends ConverterRule {
    public static final RwLogicalFilterScanConverterRule INSTANCE =
        Config.INSTANCE
            .withInTrait(Convention.NONE)
            .withOutTrait(LOGICAL)
            .withRuleFactory(RwLogicalFilterScanConverterRule::new)
            .withOperandSupplier(t -> t.operand(LogicalTableScan.class).noInputs())
            .withDescription("RisingWaveLogicalFilterScanConverter")
            .as(Config.class)
            .toRule(RwLogicalFilterScanConverterRule.class);

    protected RwLogicalFilterScanConverterRule(Config config) {
      super(config);
    }

    @Override
    public @Nullable RelNode convert(RelNode rel) {
      LogicalTableScan source = (LogicalTableScan) rel;

      TableCatalog tableCatalog = source.getTable().unwrapOrThrow(TableCatalog.class);

      return new RwLogicalFilterScan(
          source.getCluster(),
          source.getTraitSet().plus(LOGICAL),
          source.getHints(),
          source.getTable(),
          tableCatalog.getId(),
          tableCatalog.getAllColumnIdsSorted(),
          tableCatalog.isStream());
    }
  }
}
