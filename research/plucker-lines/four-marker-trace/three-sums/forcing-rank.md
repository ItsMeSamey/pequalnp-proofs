# A rank bound for coordinates forced in opposite roles

Let a binary matroid M have disjoint cycle–cocycle assignments (c,d) scored by L(c)+D(d). Write P=im L and Q=im D. Suppose q and r are attained. On a set S, every q-witness has c identically one and every r-witness has d identically one. Fix any q-witness with dual support B and any r-witness with primal support C. Then S avoids both B and C. With T=C∖B, the bound is

$$|S|\leq \dim P+\dim Q+r(C)-r(T).$$

Indeed a cycle of M deleting B, of zero L-score, may be added to the q-witness while fixing its cocycle. It vanishes on S by forcing. Hence restriction to S on this cycle space factors through L and has rank at most dim P. Its rank is at least |S|−r(S∪T)+r(T): every dependency on S modulo the span of T lifts to a cycle supported on S∪T, disjoint from B. On the dual side, restriction to S on cocycles vanishing on C similarly factors through D. Its rank is exactly r(S∪C)−r(C), by restriction of linear functionals annihilating span(C) to the images of S in the quotient.

Adding the two inequalities gives the sharper estimate

$$|S|\leq \dim P+\dim Q+r(C)-r(T)-[r(S\cup C)-r(S\cup T)].$$

The bracket is nonnegative because T is contained in C. The argument holds for every choice of the two witnesses, including circuits or cocircuits of size one and empty forcing sets.
