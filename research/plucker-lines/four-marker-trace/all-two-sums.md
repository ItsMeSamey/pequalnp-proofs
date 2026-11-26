# Arbitrary four mixed markers reduce to three-connected binary matroids

Let a binary matroid be a proper two-sum of pointed A and B with nonloop, noncoloop port e. A model is a disjoint cycle and cocycle with arbitrary four-bit linear scores. Write A_m,B_m for sets of local scores at m=(c_e,d_e) in the three states 0=00, C=10, D=01. The target p is attainable exactly when A_m meets p+B_m in some state. Local cycle–cocycle orthogonality forces a restriction disjoint on all ordinary elements to be disjoint also at its single port. Matching local models glue.

For either side compute P and Q, the linear images of pure cycles and pure cocycles having zero port bit, and U=P+Q. Write t_C,t_D for the scores of any pure cycle and pure cocycle through e and t_0=0. Every mode's scores lie in t_m+U. Zero-mode scores include P∪Q, C-mode scores include t_C+P and D-mode scores include t_D+Q, with explicit pure witnesses available by linear algebra. If U=0 on a side, all three sets are singletons whose unique values form an affine score function of c_e,d_e, absorbed in the other side for a single four-marker call. Hence assume both U nonzero.

A coupled pair query on A tests whether A_0 meets {a,a+h} OR A_C meets {b,b+h}, for arbitrary a,b and h≠0. Pass to A/e, which represents exactly the modes with d_e=0. Since e is nonloop every quotient cycle has a unique linear filling at the port. Add (a+b)c_e to the corrected score, project along h, and query target a modulo h. This uses three markers and reports which actual mode and score succeeded. Dually, deletion couples modes 0,D. Correct the underlying score by ordinary linear coordinate transfer in both cases.

## The zero mode

Cover p+P_B by pairs in each positive-dimensional P_B (any fixed nonzero direction in P_B suffices). Couple each zero-mode pair to a C-mode pair of the same difference in p+t_C^B+P_B. Either outcome immediately glues with a known pure B witness. Repeat for p+Q_B using deletion and D. The union is covered even if one space is zero, since the other contains zero. On failure A_0 is disjoint from p+(P_B∪Q_B).

For b in U_B outside P_B∪Q_B, write b=u+v with 0≠u∈P_B and 0≠v∈Q_B. Test the A_0 pair {p+b,p+v}, coupled to a C-mode pair in p+t_C^B+P_B differing by u. The second zero-mode outcome is impossible. A C result again yields a global positive witness, while any other result determines whether p+b belongs to A_0 and supplies its witness when present. This computes A_0 on all of p+U_B. Reverse to compute B_0 on p+U_A, and check the zero-mode intersection. Early positives are valid at every stage.

## The other two modes

For m=C,D, let V=(t_m^A+U_A)∩(p+t_m^B+U_B). For h≠0 differing between points of V, write h=u+v with u∈P_B,v∈Q_B. Both are actual B_0 scores, so after the failed zero-mode comparison A_0 misses p+u and p+v. Using this pair at zero answers any pair at state m on A with difference h by contraction or deletion. Reversing and translating by p gives the same oracle for p+B_m on V.

When V has at least four points, query all pairs on both sides. For at least two absent points, negative pairs identify all absent ones, and pairing a present point with an absent one yields its witness. With no negative pair the actually recorded witnesses miss at most one point. An exact-versus-exact comparison is direct; two dense witnessed sets intersect, and a dense set meets any set with at least two witnessed points. The only outstanding possibility is an exact singleton against an unrecorded dense point, leaving one specified local lookup with its opposite partner known.

Empty V rejects this mode. If V has one or two points then dim(U_A∩U_B)≤1. Since the ambient dimension is four, at least one of U_A,U_B has dimension ≤2. On this side obtain the full mode table using one state equation and at most two score rows on its known coset. The state equations are c_e=1 for C, d_e=1 for D and c_e+d_e=0 for 0; port-disjointness excludes 11. Two remaining candidates are handled by the opposite pair oracle; one is an outstanding lookup with an actual partner, and zero rejects the mode.

## Aggregating the remaining questions

Each outstanding mode has one specified membership on just one side and an actual witness for its opposite partner. If A has obligations, choose one actual score b_m in B_m for each of the three modes. In each mode assigned to A choose the required partner, and elsewhere choose any pure baseline. The map m↦b_m is affine on 00,10,01. Add it to A's score and query p with four ordinary markers. Every positive gives a genuine global witness by gluing, irrespective of the returned mode. Failure rules out every assigned obligation at once. Perform at most one analogous B query. Thus each child receives at most one hard query, retaining only four mixed markers with freely changed labels.

Recursive application on a supplied proper two-sum decomposition has linear hard-call count because |ground set|−2 is additive across the two pointed children and positive on nontrivial pieces. A standard connected matroid decomposition has three-connected, circuit, or cocircuit torsos. The latter two are tractable directly (or by regular-matroid algorithms). Direct sums use the ordinary component rule. The unrestricted three-connected binary case remains open.
