# A three-column certificate for an antichain of neutral neighborhoods

Start in the normalized even support of the [main note](README.md), without a rank bound. Suppose the neutral neighborhoods restricted to Q₀ are nonempty and pairwise incomparable under inclusion. A target exists with one P₀ vertex, at most two neutral vertices, one Q₀ vertex and two Q₁ vertices.

For a P₀ row, take a Q₁ vertex of entry zero with signature s and one of entry one with signature t. Suppose t is nonzero and differs from s. If i belongs to t outside s, choose neutral i and any Q₀ neighbor of i. These two left vertices and three right vertices have even degrees. Otherwise t is properly contained in s. Choose i in t, j in s outside t, and a Q₀ neighbor of j outside the neighborhood of i. With left vertices (colored,i,j) the three columns have restrictions (1,0,1), (0,1,1), (1,1,0). This proves the degree and marker conditions.

Such a row and pair must occur. Every P₀ row has odd opposite weight, whereas |Q₁| is even, so it has a zero. If every row failed, any row positive at a nonzero t could have zeros only at t. If two distinct nonzero signatures occur in Q₁, the other signature then must be positive too, forcing no zero at all. Thus all P₀ rows would vanish on every nonzero signature, violating the prescribed XOR on an odd-weight signature in Q₁. Such a signature exists because total neutral incidence there is odd.

If Q₁ has exactly one nonzero signature t, its multiplicity and its weight are both odd by that same incidence count. There are also an odd number of zero signatures. Every row touching t would contain all zero signatures, so its odd opposite weight would leave an even number of ones on the t columns. Rows avoiding t contribute zero there. Yet the column XOR prescribed on each t column is one, and their number is odd. This contradiction completes the proof.

The condition permits arbitrarily many independent neutral rows, for example when Q₀ contains all unit signatures. Enumerating the proposed supports gives a polynomial witness algorithm. The structural condition need only hold in one normalized feasible support to guarantee this certificate.
