# Deterministic mixed-weight feasibility with a balanced filling subspace

Let V be a binary vector space spanned by the columns of a matroid. Distinguish the primal root t and the dual root s. For an anchored model, d is a covector with d(s)=1 and d(t)=0; the primal word is t plus ordinary columns of sum t, all annihilated by d. Its objective is its primal label sum plus d(u) for a prescribed moment u. A prescribed set E of ordinary elements spans F, and its primal labels agree with a linear functional on F. Extend that functional to V, and add it to all primal labels. Cycle weights do not change and E has zero labels. Exclude distinguished occurrences s,t from E.

Assume that for every linear functional d on F, the columns of E killed by d span F∩ker d. Write k=dim(V/F). Given a target b, do the following:

1. Enumerate subsets I of at most k+1 ordinary elements. Discard I unless t+sum(I) belongs to F.
2. Solve the linear equations d(t)=0, d(s)=1, d(v)=0 for v in I, and d(u)=b+ℓ_t+sum_{i in I}ℓ_i.
3. If solvable, take any such d and represent t+sum(I) by columns of E∩ker d. Symmetric difference of those fillers and I, plus t, is the required model.

Conversely, fix a true model and its d. Its ordinary chosen columns in (V/F)⊕F₂ sum to (t mod F, b+ℓ_t+d(u)). Any binary representation of a target in this space can be pruned to an independent subfamily, of size at most k+1. These columns therefore pass both tests. Runtime is O(n^(k+1) poly(n,dim V)), including witness reconstruction.

A directly checkable sufficient certificate for the filling property consists of ordinary columns representing a basis z_i of F and each z_i+z_j, with additive labels. For a given d, zero-evaluation basis elements span the zero-coordinate part; all pairs of the one-evaluation coordinates span their even-subset subspace. Together these generate the entire kernel. The theorem also covers other supplied sets satisfying the filling property. One may verify an arbitrary such set by enumerating functionals on F when its dimension is small. No unbounded-rank recognition algorithm for the general filling property is assumed.

More generally, with p affine primal label conditions and any number of affine dual tests on d, assume that the p primal labels on E agree with p linear functionals on F. Gauge them off. Enumerate ≤k+p ordinary columns, preserving all p projected primal labels, and solve the dual tests linearly. The same proof permits prescribed right-hand sides that are affine functions of d. The search is parameterized by the codimension and number of primal tests, and the dual tests enter only the polynomial-size linear systems.

The requirement concerns actual ordinary columns with additive labels. Contraction of virtual sums alone does not provide the filler witnesses used in step 3.

## Fixed-parameter algorithm in the lifted space

Let L=V⊕F₂^p include every primal label, and let the i-th ordinary column be a_i=(v_i,ℓ_i). The target is T(d)=(t,b+ℓ_t+Md), where b,ℓ_t,M are given and d(t)=0 is one of the linear dual tests. Eligible columns obey d(v_i)=0. It suffices to supply ordinary filler columns in a subspace W⊆L such that for every d their eligible members span W∩ker(d,0). This includes any set of ordinary points of W forming a strong blocking set, which intersects every hyperplane of W in a spanning set. Explicit strong blocking sets can have size linear in dim W over the binary field. [Alon, Bishnoi, Das and Neri, Transactions of the AMS](https://doi.org/10.1090/tran/9205).

Set h=codim_L W. Bucket the ordinary columns by their projected vector in L/W. Enumerate the linearly independent type sets I of size at most h, including the empty set. For a given I, first impose the affine equation sum(I)=T(d) mod W and all dual tests. For each type in I, the bad duals obey d(v_i)=1 for every ordinary representative i of that type. This is an affine flat, possibly empty. Count candidates outside the union of the at most h bad flats by inclusion–exclusion; each intersection requires only the rank of a binary affine system. A positive count yields d by fixing one dual coordinate at a time and repeating the count. Take an eligible representative for each type. The remaining target residual is in W and is killed by (d,0); represent it in the eligible fillers by Gaussian elimination. Taking symmetric difference gives a witness even if columns coincide.

Conversely a genuine solution's projected eligible columns span its projected target. Choose an independent subfamily representing that target. Its types occur in the enumeration and the original d survives. Thus this method finds a model or decides infeasibility in 2^{O(h²)}poly(input) deterministic time. In the balanced setting above one may take W to be the graph of the common linear labeling on F; then h=codim_V F+p. More generally W may contain pure label directions. The theorem does not require an algorithm recognizing arbitrary strong blocking subsets.

For projected-switch soundness alone a balanced complete-graphic ordinary contraction flat yields a separate application of the rank-seven computation. For any two genuine opposite covectors, label each basis pivot by its two-bit joint evaluation. Contract zero-evaluation pivots and the correctly labeled differences within every remaining class. These ordinary columns have zero dual value in both models. The contracted subspace has codimension at most three in the chart's ordinary contraction flat, so the remaining entire chart has ambient rank at most seven. If triple sums also have the right labels, ordinary kernel relations of length at most three span the full joint kernel and rank at most six suffices.

## A subspace sum counts all feasible dual covectors

Let Q=L/W, h=dim Q, S(d) denote the span of all eligible projected columns, and y(d) the image of T(d) in Q. The following count uses each subspace R⊆Q once. For c≥1 set a(c)=−∏_{j=1}^{c−1}(1−2^j). The number of viable d equals

    number of d satisfying the base tests
    + sum over proper R⊂Q of a(codim R) times the number
      of base-test d with S(d)⊆R and y(d) outside R.

Compute the latter count as a difference. The test S(d)⊆R sets d(v_i)=1 for each projected column outside R. On this affine solution set, additionally imposing y(d)∈R is linear affine. Both counts are zero or powers of two.

For a fixed dual value, expand the indicator y∈S as the sum over U containing y of the indicator S=U, then invert the subspace containment order. The coefficient of the term for S⊆R is ∑_{R≤U, y∈U} μ(R,U). If y∈R the coefficient is one at R=Q and zero otherwise. For y∉R, set c=codim(R). The number of choices of U/R of dimension j containing the specified line is the Gaussian binomial [c−1,j−1]₂. Using μ(R,U)=(−1)^j 2^{j(j−1)/2}, the sum is −∏_{j=1}^{c−1}(1−2^j) by the finite binary binomial identity. This proves the formula even when the target varies with d. Enumerating canonical row-echelon bases lists every subspace once in 2^{h²/4+O(h)} time; linear algebra and the bit sizes of the signed integer accumulators add only polynomial factors. The same counting evaluation under partial dual assignments gives a witness via self-reduction. The output counts covectors admitting witnesses, independently of the number of primal witnesses for each.
