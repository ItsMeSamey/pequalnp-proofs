# Indexed comparisons in paired shells

Each physical comparison has its own edge ID. Two comparisons form a shell requiring at least one endpoint difference to equal its requested parity. Signed raw-copy pins are contracted with offsets. Loops and parallel edges retain their IDs.

The balanced-block solver accepts balanced graphic blocks and signed simple cycles. Each negative cycle chooses a single failure, with distinct shells enforced by matching. Unsupported complex unbalanced blocks raise an exception. The branch solver gives a total decision algorithm by guessing relative signs of the degree-at-least-three vertices inside those blocks. Its runtime is polynomial in raw size times the exponential bound in branch-vertex-identification.md.

The maximal-cycle autarky solver produces a residual with original shell IDs plus a conditional raw witness lift. Its proof describes handling interior articulations and cross-block shell pairs. These transformations preserve decision and recover a physical witness. Choosing a single repair can change model counts.

The mux and rail sources give exact reductions of arbitrary gates including a one-block construction with private, existentially eliminable connectors. Indexed multiplicities matter even when the simple support is a cactus. No bound on the general branching exponent is assumed.

Run check_indexed_blocks_04.py to replay the independent exhaustive small controls and original NAND checks. signed-block-sources.md gives the prior literature and pin convention.
