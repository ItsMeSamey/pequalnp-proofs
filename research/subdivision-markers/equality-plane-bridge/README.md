# Exact plane recognition and the cost of private coloring pins

## Equality spanning is the exact four-name plane query

Suppose four independent named columns span U and the required trace is a plane H in U. Choose a complement J of H in U, and coordinates outside U. Write each ordinary column as (q_e,h_e,o_e), where q_e is private, h_e is in H, and o_e is in J≅F₂². Put W=span{q_e}, V=W⊕H and t_e=(q_e,h_e). Identifying a full named kernel with its corresponding physical trace is valid here because the original named columns are independent.

**Equivalence.** There exists an ordinary subset whose span meets U exactly in H if and only if some linear map s:V→F₂² vanishing on H has the property that the t_e with **s(t_e)=o_e** span V.

In a trace witness every linear combination with private sum zero has out-of-plane value zero. Hence the out-of-plane coordinate on its span factors through a linear map on its private image. As long as this image has rank less than dim W, add an ordinary column with independent private projection and extend the map using its offset. Adding the column creates no new private-zero combinations. When done, the private image is W and the ordinary trace still contains all H. Forgetting J now gives all of V. Extend the map from W by zero on H to obtain s. Conversely a spanning equality set lifts to the complete graph of s on V, whose trace at q=0 is exactly H. If the t_e fail to span V the condition rejects directly.

Conversely any equality-spanning problem with two independent pinned directions and two output bits can be encoded this way. Extend the prescribed values on the pins to any linear map, subtract it from the offsets to make the pins zero, choose W complementary to the pins, and attach the two outside label axes. These are polynomial-time representation changes. This formulation retains common physical lifts for shared private directions. In particular, let the four physical t_e be the coordinate basis e₁,…,e₄, pin H=span(e₁+e₃,e₂+e₄) to zero, and set o₁=01 with other offsets zero. The two lanes {e₁,e₂} and {e₃,e₄} each project independently modulo H and pack a full basis. Full equality would fix all four basis values, violating the first pin. [Unequal-value spanning algorithm](../binary-aggregate-selector/README.md)

## A coloring construction with a growing pin space

For a loopless undirected graph give each vertex v its own direction x_v and all four offsets at that column. Give each edge e=uv a private direction p_e and three copies of p_e+x_u+x_v, with the three nonzero offsets. All live in the direct sum of vertex and private edge spaces. The active vertex columns always span the vertex space. Each edge's private coordinate is spanned exactly when the pair at that edge is nonzero. With all private directions pinned to zero this gives ordinary four-colorability. Four-colorability is NP-complete, for example by adjoining one universal vertex to an instance of three-colorability. [Garey, Johnson and Stockmeyer](https://doi.org/10.1016/0304-3975%2876%2990059-1)

Let Q be a nonempty affine set of two-bit edge values permitted by constraints on the private sites alone. A full equality-spanning map exists precisely when some g∈Q and vertex colors χ satisfy χ_u+χ_v+g_e≠0 on every edge. The result below allows scalar linear checks coupling the two private lanes.

## Sharp linear pin bound on an explicit NO family

Let G be the join of adjacent hubs A,B with an odd cycle of length l≥3. It has n=l+2 vertices, m=3l+1 edges and chromatic number five. A two-bit edge assignment is called balanced when both binary lanes are cuts, equivalently when its values are differences of vertex potentials.

**Lemma.** A corrected four-coloring for edge values g exists exactly when g is unbalanced.

A balanced assignment can be absorbed into vertex colors, giving the impossible ordinary coloring. For the converse, add a suitable vertex potential to normalize g to zero on the spanning star at A (including AB). Such switching preserves corrected colorability. Any unbalanced g has a nonzero value on a B-to-rim spoke or a rim edge.

If the spoke Bv has value t≠0, color A with 0 and B with t. After checking the two edges to the hubs, every rim vertex has a list of at least two colors, and v has at least three because both its hub edges forbid 0. Greedily color around the rim leaving v last. Each already colored neighbor excludes one value, so each intermediate vertex can be colored; at v at most two colors are excluded from its three-element list.

If every B spoke has zero gain, select a rim edge of nonzero gain g₀ and color B with a nonzero t different from g₀. Each rim vertex now has the same two-element list complementary to {0,t}. The difference of any two colors in this list is either 0 or t. Thus the selected edge is automatically proper. Color the remaining path greedily from its two-element lists. Undo the switching to obtain a corrected coloring for the original gains.

Consequently the compressed construction preserves the NO answer exactly when Q lies inside the product of the two cut spaces. That space has codimension 2(m−n+1)=4l over the binary field. Any nonempty affine Q defined by scalar equations must therefore have at least **4l independent checks**. Checking all fundamental cycles in both lanes attains this bound. If the same rank-d private-pin matrix is imposed on both lanes, this gives the exact threshold **d=2l**: its row space must contain the graph's full cycle space. The criterion permits arbitrary nonlocal recombinations of the originally zero private pins. Conditions mixing vertex colors and private shifts can have different behavior; for instance directly pinning a tested column to zero trivially kills its edge even on a colorable graph. A different compiler would need its own soundness and completeness proof.

## Controls

Run `python check.py` and `python check-gains.py` with the sibling binary aggregate and elimination helpers. On 116 random full-private-span four-name instances, direct physical subset enumeration agreed with equality spanning; unequal spanning gave a different verdict 53 times. The source tests checked every nonzero binary gain syndrome at rim lengths 3, 5 and 7 (63, 1,023 and 16,383 syndromes), verified the actual physical active-column rank, and reconstructed valid colors on perturbed graphs. A separate test checked 7,096 two-bit gain assignments including every normalized two-bit assignment for the length-three rim.

This rules out the private-pin projection of the displayed four-coloring reduction at fixed pin rank. The unrestricted two-pin, two-output equality-spanning problem, equivalently this four-name plane query, remains open. Its NP-hardness would require a distinct reduction.
