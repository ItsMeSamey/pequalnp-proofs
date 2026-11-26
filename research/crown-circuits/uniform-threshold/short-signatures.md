# Retaining short singleton signatures

For the three-layer circuit of `three-level-matching.md` one can achieve

    C(n) ≤ 2n+√(2n)+(5/4)2^(9/10)n^(3/10)+O(n^(7/30)).

Set t=√(2n), A=2·8^(−4/5), v=ceil(t+A t^(3/5)+L t^(7/15)), w=ceil((8v³)^(1/5)), z=ceil(v^(7/15)), where L is a sufficiently large absolute constant. Condition the random graph R in the previous proof on Δ≤10v/w+1. For k=ceil(10v/w), its previous elementary union bound w(2ev/(wk))^k is exponentially small. Thus the same first-stage loss applies, and Δ=O(v^(2/5)). Let F be the family of distinct retained four-element vertex sets of R, each spanned by two disjoint edges.

Inject [w] uniformly into the edge set of K_z as before. Each member of F activates at most eight endpoints, including when its four edge images intersect. For each unordered pair of distinct members of F for which all combined endpoints number at most eight, discard one member. The remaining singleton signatures are rejected by threshold nine, while every two distinct retained members are accepted. The number of discards is at most the number of bad pairs.

If the two four-sets share r points (0≤r≤3), they use d=8−r distinct edge images. For each fixed pair the probability of at most eight endpoints is O(z^(8−2d)): pick eight endpoints in O(z^8) ways and choose d ordered distinct edges among them in O(1) ways; all ordered samples number Ω(z^(2d)). The counts of candidate pairs for r=0,1 are each O(v^4). For r=2 it is O(v³), by the existing pair codegree bound v+Δ² and total pair codegree O(v²). For r=3, the maximum number of four-sets containing any fixed triple is ≤3Δ: at least one edge of the retained matching lies wholly in the triple, and after choosing it the last endpoint is a neighbor of the third member. Total triple codegree is 4|F|=O(v²). Hence the expected total loss is

    O(v⁴/z⁸+v⁴/z⁶+v³/z⁴+v²Δ/z²)=O(v^(22/15)).

The terms have exponents 4/15, 6/5, 17/15 and 22/15 respectively. Intersections in the first graph cost O(v²/w)=O(v^(7/5)). Its four-cycle loss remains at most A v^(8/5)(1+O(1/w)), with conditional probability error exponentially small. Expanding at t changes its leading term by O(t^(6/5)) and all residual terms are O(t^(22/15)). Choosing L beyond the absolute loss constant leaves at least n labels. The physical gate ledger is unchanged. The final detector costs O(z)=O(t^(7/15)), proving the asserted bound. This is an upper bound with the previously established construction coefficient.
