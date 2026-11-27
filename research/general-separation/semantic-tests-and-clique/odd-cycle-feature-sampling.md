# Every proper feature sample admits a spurious annihilator

An explicit polynomial-size dictionary of linear-size Boolean formulas represents the independent-bank AND of indirect lookups with all coefficients equal to one half. Every proper subset of this dictionary admits a signed row combination that vanishes on all its features and has target response one. The same statement holds over every field of odd characteristic.

## Odd-cycle responses

On t odd tag values numbered from 0 to t−1, with t≥3, feature E_j indicates the two endpoints of edge (j,j+1) modulo t. Every row has two active features. The constant-one vector is therefore the half-weight sum of all columns. These coefficients are unique over the rationals and in odd characteristic: a zero combination satisfies c_j=−c_{j−1} around an odd cycle, forcing all c_j=0.

Omit edge j. Traverse the remaining path from vertex j+1 to vertex j and give successive vertices signs +1,−1,+1,…,+1. The signs sum to one. Every edge except j joins opposite signs and has response zero; edge j has response two. Thus this dual works for any sampled dictionary missing j. When just j is omitted, annihilation on the path and normalization to total mass one uniquely force these weights, supported on all t rows.

## Full-cube lookup realization

Fix r≥2 independent banks. In each bank take m=2^k payload bits and a power-of-two number P=Θ(m/log m) of k-bit pointer words, with its own primary row index I_a. Let F be the AND of the r selected payload bits. The input length N is Θ(rm). On a primary tuple α let H_α assert I=α and that all selected payloads on those fixed pointer rows are one. A multiplexer formula on each bank uses O(m) leaves and the row guard uses O(log P). The H_α have disjoint support and sum to F.

Take t=m−1 for m≥4. On rectangle α, read a k-bit pointer word other than the selected one in the first bank, for instance at α₁+1 modulo P. Fold its largest code into tag t−1 by taking the minimum of its unsigned value and t−1. Every tag occurs on a YES input of the rectangle, as witnessed by all-one payloads. Tag endpoint membership uses at most three fixed-code equality tests and O(log m) leaves. For every rectangle include its t features H_α E_j. The dictionary has S=P^r t members, polynomial in N for fixed r, each of size O(N). Both t and the forced number of rows in a single-omission path witness grow linearly in N for fixed r.

On every input the unweighted sum of these S features is exactly 2F. For any omitted feature take one YES row per tag from its rectangle and the alternating path weights above. Other rectangles vanish there. This yields the asserted dual for every proper sampled dictionary. Over the full dictionary, linearity and the half-weight representation rule out any annihilator with nonzero target response. Indeed the full coefficient vector is unique by the disjoint YES-row blocks. If just one feature is omitted, the normalized witness needs at least t distinct raw rows even if it can use arbitrary inputs: NO rows contribute neither features nor target; other complete rectangles contribute zero total YES mass by their half-weight identity; the remaining rectangle must then have alternating aggregate mass on every tag.

Under independent uniform sampling with replacement, the expected number of draws needed to cover the dictionary is S times the S-th harmonic number, from the geometric waiting times for each successive unseen column. Sampling without replacement requires S draws for this coverage criterion. This concerns inference from the sampled span. The target also has the separate exact dictionary consisting of the P^r formulas H_α with coefficient one. More generally, an annihilator for the union of all allowable Boolean atoms is a statement about their entire span, whereas a bound on S-term sums can admit different witnesses for different S-column lists.

## Modular carries and checks

At an odd prime p, the standard representative of one half is (p+1)/2. The lifted integer sum is (p+1)F and its carry, obtained by subtracting F and dividing by p, is F. Only the levels zero and one occur. The target here is an AND of independent bank outputs. The balanced XOR target in the carry-spectrum theorem has different correlation properties. [Carry-spectrum theorem](modular-carry-spectrum.md)

The checker verifies every proper sampled edge set for t=3,5,7,9 over the rationals and modulo 3,5,7, together with all 1,024 inputs of a small two-bank lookup in which every rectangle is split. [Executable checker](odd_cycle_feature_sample_check.py)
