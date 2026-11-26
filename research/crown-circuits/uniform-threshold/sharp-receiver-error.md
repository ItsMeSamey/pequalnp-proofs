# Quantitative error for the effective receiver argument

Use the lemmas of `unrestricted-sharp-receiver.md` and write b=(5/4)2^(9/10). For unrestricted monotone threshold two the effective receiver proof gives

    2n+√(2n)+b n^(3/10)−O(n^(1/4)) ≤ C(n)
      ≤ 2n+√(2n)+b n^(3/10)+O(n^(7/30)).

The upper bound is `short-signatures.md`. For a regular minimum use the notation of the sharp lower proof. The published exponent and upper give E=Θ(h^(3/5)) uniformly. We have K=hE+O(h+E²), d=O(E), h=t+O(E), and at most O(hE) missing shared pairs.

At both trimming stages for uniform neighbor qualifications, use the fixed cutoff h^(4/5) for missing or cold high pivots per row. Total deficit O(hE) removes O(h^(4/5)) rows each time. The impure, AND-reader, and high-fanout exceptions cost O(E), since d=O(E). The private–private exclusion from `unrestricted-shared-cover.md` costs O(a+√(L+1))=O(h^(4/5)): remove at most a rows feeding two private arms of the same AND, then a random choice of one arm per AND retains at least one quarter of the remaining private–private rows, among which there is at most one actual raw. Both degree-one prunings cost O(E). Thus g'=h−O(h^(4/5)). Every use of the uniform row qualifications to bound effective OR columns now has O(h^(4/5)) exceptions. Each effective OR column costs h−O(h^(4/5)) incomparable missing pairs outside H×H. The shared AND charge gives, with z=L/(hE),

    w ≤ (1−z)E+O(E h^(−1/5)).

The initial four-cycle estimate is O(hE). With T the total codegree, this gives T=O(h^(7/5)); its lower bound 2g'²/w−g' gives T=Ω(h^(7/5)). The C4-active cold exception charge is O(h^(7/5)) as well. By Cauchy–Schwarz the codegree mass on adjacent pairs is O(√(g'(T+hE)))=O(h^(13/10)), at most O(h^(−1/10)) of T. The nonadjacent wedge mass is therefore at least (2g'²/w)(1−O(h^(−1/10))). Cauchy–Schwarz on nonadjacent vertex pairs, subtracting O(T) when passing from squares to binomial counts, yields

    L+O(h^(7/5)) ≥ (2−O(h^(−1/10)))h⁴/w⁴.

Here O(T) relative to h⁴/w⁴ costs at most O(h^(−1/5)), since w=O(h^(3/5)); replacing g' with h costs the same. Divide by hE and substitute the column budget. Endpoint excursions of size O(h^(−1/5)) and additive perturbations to z or 1−z cost O(h^(−1/5)) by bounded derivatives. Maximizing z(1−z)^4 on [0,1] now gives E ≥ (5/4)2^(3/5)h^(3/5)−O(h^(1/2)). Replacing h with t incurs O(t^(1/5)). Along a sequence of nonregular minima the three-gate deletion alternative reaches a regular minimum on m=n−O(√n) inputs. The surplus s(n)−√(2n) dominates s(m)−√(2m); also t(n)−t(m)=O(1). This transfers the same error to every sufficiently large n.
