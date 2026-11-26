# One clean-column signature and rank-two dual gains

In the one-A-exception setting write Q={0,1,2,3}, b=4, D(A)=1, r=b+1. The circuit B has an odd number m>1 of clean nonbasis columns, each with primal score b. Its exceptional basis rows have identical all-one restrictions on Y and no support on the A exception. Their fundamental cocycles lie in B. Their number is at most two by the supported-subcode injection together with the A circuit, and is odd since B is a cocycle whose bits on Y are all one. There is exactly one such B basis position.

Each clean row has even weight, so has a zero somewhere. No clean gain is 1, since at a zero column the associated fundamental primal circuit and dual cocircuit could attain r, violating reverse uniqueness. The sum of the clean gains is 1, so gains 2 and 3 both have odd multiplicity. Their rows cannot share a zero, for the same reason using their two dual toggles. As m is odd and both row weights are even, their Gram inner product is one. Each gain class is independent in the Eulerian Gram graph, since same-gain rows have the same exceptional entry and hence comparable clean supports. The size of X is odd by cycle–cocycle orthogonality of A with itself. Thus the zero-gain class also has odd size.

Every gain-2 row sees all gain-3 rows, and consequently an odd number of zero rows. At each zero vertex z the numbers of its gain-2 and gain-3 neighbors have the same parity. The sum over z of the products of these two counts is therefore odd. A rainbow triangle exists. It is induced-even and matches all three class parities, so reverse uniqueness forces X to equal that triangle. Its Gram rank is two. Since the clean rows span the full even-weight subspace on odd m and its dot pairing is nondegenerate, m−1=2. Up to ordering N is the three-by-three J−I. The whole four-by-four fundamental rectangle is J−I, using the all-one exceptional borders and their zero common corner.

In this chart place dual clean gains 0,2,3 and primal clean gains b on the first three indices; let the last index have primal gain α=L(A) and dual gain β=D(B). For J−I an assignment (x,y) with x=y of odd size is legal. Two disjoint even sets are legal as well. Four families of legal assignments now exhaust the total score space:

* y empty gives Q.
* x=y an odd clean subset gives b+Q.
* x=y equal to the exceptional index together with an even clean subset gives α+β+Q=α+Q.
* y consisting of the exceptional index and one clean index, with x empty or the two complementary clean indices, gives b+α+Q.

Here the three different clean gain pairs sum to the three nonzero elements of Q. These families cover span(Q,b,α). If it has rank four there is no missing score. Otherwise α belongs to Q or b+Q; respectively the fourth or third family also attains r with the exceptional primal bit on, violating uniqueness of the reverse witness. Thus the assumptions of a missing score and opposite unique witnesses are incompatible.
