# Warm gates dispensable on positive theta flags

Fix the single theta and construct the source-cover circuit of theta-source-cover.md. Count its physical slots before trimming dead code, or first trim and include all trimmed slots in the savings. Let Z be all remaining gates that vanish on every one of the 3k positive flags, evaluated after rewiring and source selection. All retained raws occur in some flag; the output is not in Z.

Set all Z outputs to zero. Positive evaluations remain unchanged throughout by forward induction; negative outputs only decrease. This eliminates all Z gates, and each remaining reader outside Z with a Z input. Every such reader is an OR with exactly one Z input. With b distinct such gates the extra saving is |Z|+b. There is no overlap with earlier removals. Let z_i count Z gates with i operand slots belonging to Z. Then their excess fanout in the intermediate circuit is F'_Z=z_2+b−z_0, giving |Z|+b=F'_Z+2z_0+z_1. Use actual intermediate fanouts, since earlier rewiring changes original outgoing slots. If untrimmed, the algebra permits negative fanout excess for dead gates.

Thus δ≥F_C+E_D+(c1−H_D)+2(c0−t)+|Z|+b. When dead code was trimmed before this step, add those separately removed gates. Independent review by /root/incidence/audit confirmed the positive-dead criterion and physical reader disjointness.
