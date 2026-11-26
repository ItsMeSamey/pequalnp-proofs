# Nonlinear gate count for Hamiltonicity on row-one-hot inputs

An input specifies one successor for each of N vertices. The predicate accepts when the resulting map is a single permutation cycle. Self-loops are allowed as inputs. In the one-hot encoding there are N² input bits with one set bit per row. In the binary encoding there are N⌈log₂ N⌉ input bits, with any out-of-range label rejected. Let r count distinct two-input AND gates in a Boolean circuit over XOR, AND and constants. XOR gates and fan-out have zero price in this measure.

**Bounds.** The predicate needs Ω(N log N) AND gates and admits a uniform construction with O(N log⁴ N) AND gates in either encoding. Thus the lower bound is superlinear in the number of rows, of linear order in the binary input length, and sublinear in the number of one-hot input wires. These are gate bounds with no charge for XORs or for reading inputs.

## A one-way protocol from the circuit

Topologically order the r AND gates. Each of their 2r inputs is affine over the original bits and the outputs of earlier ANDs: expand the intervening XORs, stopping at an input or an AND output. The final output has the same affine form. At any cut of the input bits, Alice sends Bob the contribution of her raw bits to each of these 2r+1 forms. Bob adds constants and his contributions and evaluates each gate once in order. The protocol works with shared subcircuits and on a promised input domain. At a row cut, the valid label domains on the two sides form a product, so each distinct row of the communication matrix must receive a distinct message. If there are D distinct rows, then 2r+1 ≥ ⌈log₂ D⌉.

## Number of distinct residual functions

Let I be a fixed set of k rows owned by Alice, with 0 < k < N. Then

\[
D(N,k)=1+\sum_{m=1}^{\min(k,N-k)}
\binom{k}{m}\binom{N-k}{m}m! .
\]

A noninjective partial map, or one containing a closed cycle, yields the zero residual. This residual occurs, for instance, when an Alice vertex maps to itself. For any partial map with a nonzero residual, write S for its image. Bob's completing map must be a bijection from the complement of I to the complement of S. Different S therefore give disjoint supports for their nonzero residuals.

For fixed S with m = |I minus S| ≥ 1, Alice's cycle-free map consists of m disjoint paths. Their endpoints specify a bijection α from I minus S to S minus I. Every such bijection can be realized by inserting all vertices of the intersection of I and S along one of its paths. Bob's valid path systems similarly realize every reverse bijection β. Gluing succeeds precisely when βα is one m-cycle. This is the bipartite matching communication problem of Raz and Spieker. [Original paper](https://doi.org/10.1007/BF01192528)

Each α yields a nonzero residual, by choosing βα to be any m-cycle. For α ≠ α′ let δ = α⁻¹α′ and choose a point t moved by δ. Choose an m-cycle γ sending δ(t) to t, and choose β = γα⁻¹. Then βα = γ is an m-cycle whereas βα′ = γδ fixes t. Thus all m! boundary bijections induce different residuals. For m=1 the sole bijection contributes one. The case S=I has a closed component and contributes only the zero residual. Counting the possible S proves the formula. If k=0 there is only one row. If k=N and N≥2 there are two residuals, the constant output bits. At N=1 the only valid permutation is accepted.

Taking k=⌊N/2⌋ and just the term m=k gives r ≥ (⌈log₂(k!)⌉−1)/2. The formula counts residuals rather than rank. For example, with N=6 and k=3 it gives 34 distinct rows, while the characteristic-zero rank is 33. Direct cycle enumeration checked the residual formula for all 21 nontrivial cut sizes through N=7. [Cycle table generator](./onehot_hc_rank_check.py) · [Rank proof](./onehot-hc-rank.md)

## Circuit construction

In the one-hot encoding, form each binary digit of a row's successor by XOR-ing the corresponding one-hot entries. This uses no AND gates. With binary inputs, range-check each label and record a rejection flag. Pad sorting networks to the next power of two using distinguished dummy records.

Sort the successor labels and compare the sorted list with the fixed vertex list to test that the successor map f is a permutation. Keep the result as a validity bit. On a valid instance maintain at vertex i the pair (p_i,h_i), initially (f(i),i). At round j, these are the successor after 2^j steps and the least label among the first 2^j vertices of the orbit starting at i. The simultaneous update is

\[
(p_i,h_i)\longmapsto(p_{p_i},\min(h_i,h_{p_i})).
\]

To implement the lookup, sort query records (p_i,i,h_i) by p_i. Because p is a permutation on valid instances, the sorted positions align with the current table (p_v,h_v) in vertex order. Read the aligned records, update, and sort the results back by i. On invalid instances the circuit still runs for the same number of steps and its final validity bit forces rejection. After ⌈log₂ N⌉ rounds, every orbit minimum is known. A valid permutation has just one cycle exactly when every minimum equals the globally least vertex label.

A bitonic sorting network uses O(N log² N) comparators, each implementable with O(log N) fan-in-two gates on these O(log N)-bit records. This gives O(N log⁴ N) AND gates over all rounds. The initial one-hot compression may use O(N² log N) XORs and does not turn this AND count into a near-linear bound on all gates in the one-hot encoding.
