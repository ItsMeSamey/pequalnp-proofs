# Deterministic marker-parameter algorithm at bounded native dependency depth

A native guarded decision z_i may always be zero and may be one when one of its affine literal indicators g_ij is one. Suppose all dependencies are acyclic after substituting a proposed value one for self-references inside its own guard. For each literal give the generator an independent selector bit u_ij, and compute in topological order

    z_i = sum_j u_ij g_ij  over the binary field.

If no literal is true the sum vanishes; otherwise both bit values are possible. Empty guards yield fixed zero. For a genuinely free bit use a constant-one literal. Every source witness has a preimage: choose a single true literal at every one bit and zero selectors elsewhere. This works with arbitrary affine width and arbitrarily many alternatives. Fixed observations are constants; existential input bits can be included as free seed coordinates.

With fixed observations, degree ≤H on each output bit follows by induction if H is the largest number of hidden vertices on a dependency path, counting a source as one. With existential observed inputs add one to the bound. For each final clause, a disjunction of affine literal indicators, introduce fresh selectors and require their weighted sum of indicators to equal one. This test has degree at most H+1 with fixed observations and H+2 with free inputs. Take d=max(1,H+2) uniformly.

The resulting b-bit polynomial map hits the all-ones target exactly for satisfiable instances. By the low-degree density argument and Viola generator used in subdivision.md, this gives time n^{O(d)} 2^{O(d² 2^d b)} times polynomial input evaluation, polynomial in the number of literal occurrences for fixed H. Thus it is deterministic fixed-parameter tractable in terminal count b when H is fixed. If a supplied feedback set of size f leaves residual dependency height H, enumerate its values. For each fixed one bit add its guard as one more terminal; fixed zero bits need no condition. The overhead is at most 2^f and the terminal budget increases to at most b+f.

The sparse example in tree-barrier.md shows uniform sound-generator degree can grow linearly in dependency depth even when each guard reads at most two earlier bits. This upper bound does not imply an unrestricted deterministic fixed-parameter algorithm.
