# An explicit shared-gate charge for arbitrary alternation

In any trimmed physical binary scalar DAG let B be the OR gates that have a strict AND ancestor and a strict AND descendant (paths directed from inputs to output). For a native flag e define c_e as the minimum number of DISTINCT gates of B visited in any accepting proof DAG for e. At every visited OR the proof chooses a single true physical operand consistently; at every AND it keeps both. This parameter is well-defined with arbitrary fanout and repeated inputs.

Independently choose one of the two physical operand slots of every gate in B uniformly and replace all its uses by its chosen input. Every outcome C' is a pointwise underapproximation of C on the entire cube by monotonicity; hence it rejects every original legal negative. Whenever the chosen slots agree with a fixed minimum proof for e at its c_e visited switches, C' accepts e. Thus the expected number of accepted native flags is ≥Σ_e 2^(−c_e). This guarantees no new behavior on negative masks without testing a distribution of negatives.

After forwarding and trimming each C' has no directed AND–OR–AND subsequence: any remaining such OR had both an AND ancestor and descendant in the original graph and was switched. All ORs carrying AND outputs therefore lie in the final OR collector, and any OR feeding an AND takes only raw-label ORs upstream. This is exactly the layered model, with raw banks allowed. A nonempty pure bank cannot feed the collector alone since it would accept a forbidden singleton. There are at most the original O and A gates of each type in each outcome and at most 2N+O distinct source banks.

The proof of shared-bank-physical-transversal.md uses only the actual accepted flags and rejection of all legal negatives, so applies to each underapproximation with its own edge set E'. Provided log₂(2N+O)<q and q>100, it gives

Σ_e 2^(−c_e) ≤ 6O+4(log₂(2N+O))² A.

There is no gate-copy charge across outcomes: this takes expectations of a uniform upper bound valid for each physical specialization, each of which only forwards and trims. For s<Nq/100 the logarithmic condition holds automatically. In particular if at least αE flags have c_e≤k then either s≥Nq/100 or s≥αE/[2^k max(6,4(log₂(2N+s))²)]. For a fixed α>0 and k≤(1−ε)log₂q with fixed ε>0, this yields s=Ω(N q^ε/log²q). All implications retain the original one-sided negative tests, with no assumed general normalization or uniform bound on c_e.
