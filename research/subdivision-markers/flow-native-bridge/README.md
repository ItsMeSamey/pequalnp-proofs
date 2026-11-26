# Trying to turn cubic nowhere-zero flows into a constant-score native guard

With D the binary vertex-edge incidence matrix of a finite simple cubic graph, put C=ker D and H=C⊥. An ordered nowhere-zero F₂²-flow consists of a,b∈C such that the pair (a_e,b_e) is nonzero at every edge. At a cubic vertex the three nonzero values must be the three different values. This is precisely proper three-edge-colorability, an NP-complete decision problem. The literal substitution x=1+a, y=1+b turns the coverage condition into disjointness of x,y, but now both words must lie in the **same affine cycle coset** 1+C. In this coset each vertex has odd degree. Disjointness therefore forces one selected edge of each word at every cubic vertex, and the unselected edges form a third perfect matching. [Holyer](https://doi.org/10.1137/0210055)

Simply changing the second space to the affine cut coset 1+H always accepts. Each component of a cubic graph has even order. Take a join x with every vertex odd in a spanning forest. The forest is bipartite, so its edges all lie in a cut b, and x is disjoint from 1+b. Duplicating coordinates does make (c,c) orthogonal to (d,d) for all cycles c,d, but completing those diagonal subspaces to a native code S and its exact orthogonal complement S⊥ generally adds further words. The estimates below quantify what disjointness can enforce on such completions.

## A linear estimate with hidden coordinates

Let U be any code on visible and hidden coordinates, and U⊥ its exact dual. Suppose restrictions of total ranks b_P,b_Q give subcodes of U and U⊥ whose visible projections lie respectively in C₁,C₂. Then

    b_P+b_Q ≥ dim(C₂⊥)−dim(C₂⊥∩C₁).

Embed J=C₂⊥ on the visible coordinates with hidden zeros. It annihilates the permitted dual directions, so J∩U has codimension at most b_Q in J. Projection modulo C₁ on J∩U has rank at most b_P since all permitted primal directions vanish in this quotient. The displayed bound follows by comparing ranks. The same argument applies to directions of affine fibers. No assumptions on the number, meaning or dependence of the hidden coordinates are needed.

With both projected directions in C, this lower bound is δ=dim H−dim(H∩C)=rank_F₂(DDᵀ). On a simple cubic graph DDᵀ=I+Adj. Its principal submatrix on any independent set is the identity, giving δ≥|V|/4 by greedy independent-set selection.

For nonempty affine restrictions lying literally in S and S⊥ and projecting into 1+C, the exact optimal total rank under separate marginal soundness is δ+(δ mod 2). Moreover all true disjoint pairs have disjoint native lifts at this optimum. To see this, set F=C+〈1〉. The all-one vector is outside C on nonempty cubic graphs. Adjoin one affine witness to each channel's direction space. The two enlarged spaces project into F and cost at most b_P−1 and b_Q−1. The lower bound above gives b_P+b_Q≥2+δ_F, where δ_F=dim F⊥−dim(F⊥∩F). For the upper bound take

    S=(F⊥×0)+{(x,x):x∈F}.

The first-half projection of S is F+F⊥, and that of S⊥ is F: an element (u,v) of S⊥ satisfies u∈F and u+v∈F⊥. Imposing first-half membership in 1+C costs 1+δ_F primal checks and one dual check. Every (x,x) with x∈F belongs to both native spaces. For x,y∈1+C the diagonal lifts are disjoint exactly when x,y are disjoint.

For the numerical identity, use the form induced on H/(H∩C), of dimension δ and nondegenerate. Its characteristic vector w represents the functional h↦h·h=h·1; the map is nonzero because the graph is cubic. F⊥=H∩1⊥ induces w⊥ modulo the original radical. If w·w=1, w⊥ is nondegenerate alternating of dimension δ−1, so δ is odd and δ_F=δ−1. If w·w=0, w⊥/〈w〉 is nondegenerate alternating of dimension δ−2, so δ is even and δ_F=δ−2. Binary alternating forms have even rank. Thus 2+δ_F=δ+(δ mod 2).

An externally given affine translation of an entire native space changes the sharp affine statement if the fiber need not lie in the corresponding homogeneous native code. The direction bound δ still applies.

## Disjointness cannot eliminate all extra modes under literal edge decoding

Now require only that every **jointly accepted** disjoint raw pair give two disjoint perfect matchings by reading one common physical position for each graph edge. Require at least one accepted pair on a colorable instance. The condition does not assume that separately allowed raw primal or dual words are sound, or that all colorings have lifts. Arbitrary hidden coordinates are permitted. Let the native raw variables range over affine translates of complementary binary spaces S and S⊥ subject to linear score checks or pins. For a shared equation L_P p+L_Q q=t, use the two ranks with the other argument fixed. Exempt named positions can be retained among the unguarded hidden coordinates below, with their fixed linear values included in the checks.

Fix an accepted witness p,q. Write A and B for its occupied primal and dual guarded coordinates, respectively, and R for their complement among all coordinates. They are disjoint. With q fixed, changes to p must vanish on B; after projecting these changes to R, their underlying unrestricted native code is

    U=project_R{x∈S : x_B=0}.

Symmetrically, with p fixed the unrestricted projected dual code is project_R{y∈S⊥ : y_A=0}=U⊥. This follows by duality of puncturing and shortening, or by contracting A and deleting B. Imposing the actual conditional linear checks costs ranks at most b_P=rank L_P and b_Q=rank L_Q. Every surviving single-channel change gives a genuine accepted pair with the unchanged opposite witness. No independence between two simultaneous moves is assumed.

Write M₁,M₂ for the visible perfect matchings and Z for the third matching. These |V|/2 coordinates all lie in R. With M₂ fixed, a new primal word must be a perfect matching in M₁∪Z. This graph is a disjoint union of alternating cycles. On each cycle only the two alternating choices are possible. Thus all conditional primal changes on Z lie in the code C₁ spanned by the indicators of the Z-edges in those cycles. For dual changes use the partition of Z from M₂∪Z and its code C₂. Let a,b count the two sets of cycles, and let T be the binary matrix of intersection parities of their Z-blocks. Applying the linear estimate on R with visible subset Z gives the **joint-only obstruction**

    b_P+b_Q ≥ |Z|−a−b+rank T.

Indeed dim(C₁∩C₂⊥)=a−rank T. The rank arguments are constructive: compute both conditional direction spaces by elimination and test whether their projections on Z lie in the two indicated codes. Below the bound, one inclusion fails. Back-substitution produces an accepted raw pair whose visible edge words violate the matching requirement. Repeated copies synchronized in accepted witnesses may be read at any common representative.

For girth at least six, a,b≤|V|/6 and |Z|=|V|/2. In particular b_P+b_Q≥|V|/6. The overlap term improves this to 3|V|/14. Put N=|Z|, ρ=rank T. Every block in either partition has at least three entries. At least 4a−N row blocks have size exactly three and hence nonzero parity row. A basis of ρ columns covers all nonzero rows; its original blocks together contain at most N−3(b−ρ) elements. Consequently 3ρ≥4a+3b−2N, giving N−a−b+ρ≥(N+a)/3. The symmetric bound holds with b. If max(a,b)≥2N/7, one of these bounds is at least 3N/7. Otherwise N−a−b>3N/7. A single shared b₀-bit score has b_P+b_Q≤2b₀, so b₀≥3|V|/28 on this class.

Connected cubic bipartite examples exist for every integer m≥7: connect A_i to B_i,B_(i+1),B_(i+3) with indices modulo m. The three shifts give an explicit coloring. The six nonzero ordered shift differences ±1,±2,±3 are distinct, excluding four-cycles, and consecutive shifts ensure connectivity. Thus constant-score completions cannot meet this joint witness requirement over the family. A reduction preserving only the yes/no answer, an encoding using a different decoding of visible words, or extra lanes whose guards occupy the nominally free third matching is outside the theorem.

## Explicit controls

The checker forms cubic cycle bases by binary elimination and enumerates both affine flow lanes. For each valid ordered pair it independently computes the two alternating partitions and the intersection rank. A second audit used direct edge-color backtracking and constructed DDᵀ on the vertices.

| Graph | Ordered flows | δ | Sharp separate rank | Joint witness lower bounds attained in the formula |
|---|---:|---:|---:|---|
| K₄ | 6 | 1 | 2 | 0 |
| K₃,₃ | 12 | 5 | 6 | 2 |
| Petersen | 0 | 5 | 6 | no feasible source witness |
| Shift graph on 14 vertices | 48 | 13 | 14 | 6 |
| Shift graph on 16 vertices | 120 | 12 | 12 | 4, 5, 6 |

On Petersen, retain the full correct dual marginal of the displayed doubled S, but impose only the primal star parity at vertex 0. The perfect-matching spokes give dual diagonal lift (992,992). The even cut 17438 gives primal lift (17438,0), outside the required visible affine cycle coset. The words are disjoint, the native membership tests and the primal pin pass, and the source has zero flows. Edge order is outer pentagon, corresponding spokes, then inner star edges in cyclic index order.

Run `node check.js` and `python check_minor.py`; the latter verifies 1,200 ambient minor-duality identities and uses the sibling unseeded-root-states code. The lower bounds are for direct witness encodings of the stated type. They give no lower bound for arbitrary algorithms for the decision problem and do not decide P versus NP.
