# A four-track obstruction to exact two-occurrence sheet action

Suppose a compiler must implement (s,i) ↦ (s xor [σ(i)∈O],i) on every designated sheet point, for every mask, allowing arbitrary fixed permutations and extra tracks. Even for fixed output set O this is impossible with at most two controlled three-cycles per source bit.

Take four tracks, O={2,3}, and successive optional rotations g=(1 3 2) and h=(0 2 3), with forward occupant movement. Relative to all off the setting toggles the sheet transpositions at σ⁻¹(O) △ O. Direct substitution gives the empty set with both off, {1,2} for g only, {0,3} for h only, and {0,2} with both on.

Move fixed permutations to the end of the word by conjugation. Cancel the all-off permutation there. On the designated labels the resulting relative action toggles exactly the indicated pairs. Complemented controls also normalize this way by factoring out their fixed baseline cycle and using its inverse when on. Every remaining controlled occurrence is a three-cycle on a fixed triple.

To realize two disjoint transpositions with at most two three-cycles, the two supports must share exactly two points. Disjoint triples give two three-cycles, one shared point gives a five-cycle, and three shared points give identity or a three-cycle. Thus the supports' union consists precisely of the four points moved by the two prescribed transpositions, even if auxiliary tracks may have arbitrary final permutation.

From the g-only setting, both g occurrences are confined to the sheet points of tracks 1 and 2. Both h occurrences are confined to the sheet points of tracks 0 and 3. Their factors commute across controls in any interleaving. Both on therefore toggles all four track pairs, contradicting the required {0,2}. At least three occurrences of some control are necessary in this exact permutation model. This leaves possible reductions that only preserve rooted existence, including the forbidden-pairs path construction.

The checker enumerates every ordered pair of three-cycles on six labels, covering all possible supports up to relabeling, and tests the four-track calculation.
