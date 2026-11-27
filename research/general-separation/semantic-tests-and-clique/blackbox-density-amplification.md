# Adaptive black-box amplification across the hereditary half-density threshold

Fix rational 0<δ<1/2. A deterministic compiler receives m and membership-query access to unknown A⊆{0,1}^m satisfying the [prefix density condition](hereditary-witness-density.md) at δ. It may query A when producing its verifier and witness length ℓ. That deterministic verifier may itself query A on each supplied witness. The compiler purports to preserve nonemptiness and make its output empty or hereditarily half-dense.

Run the compiler on the empty oracle, then run its output verifier on all ℓ+1 witnesses of Hamming weight at most one there. Let T be the distinct m-bit queries in all these executions. Any correct compiler has

    |T| ≥ [2(1−δ)]^m.

If fewer were queried, the pruning theorem gives a nonempty δ-hereditary A disjoint from T. All adaptive compiler replies are unchanged. Thus its verifier and length are the same. The ℓ+1 verifier computations also remain identical. On the empty oracle all reject, so on A all reject. This contradicts the explicit hitting set for a nonempty half-hereditary output. Only empty-oracle values of the compiler cost and ℓ enter the argument. If the compiler spends q₀ queries and each tested evaluation spends at most q queries there, q₀+(ℓ+1)q≥[2(1−δ)]^m.

When the compiler, its output length and the evaluated runs take polynomial time in m on the empty oracle, the proof gives a single polynomial-time uniform avoiding family against that fixed compiler. On input (1^m,w) regenerate T by simulating every empty-oracle run, then form the explicit prefix trie, prune with fixed rational δ and test w in the survivors A_m. This takes polynomial time in m. For every sufficiently large m the survivors are nonempty and all recorded answers remain negative. Thus the compiler fails on each sufficiently large length, assuming it succeeds on the empty family. The decision language asking whether these A_m are nonempty is eventually constant. This tests the proposed verifier transformation.

The transcript bound covers OR repetition with interleaved witness bits and adaptive membership checks if they use the stated access. A root-density gain from repetition does not by itself establish density at every viable prefix. A transformation inspecting the circuit description of A has additional information. A randomized compiler has different quantifiers.
