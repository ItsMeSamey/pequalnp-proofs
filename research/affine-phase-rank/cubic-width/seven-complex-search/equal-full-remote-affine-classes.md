# Five computational shapes for an equal full remote code

Assume both exception flattenings on A versus BC have rank eight and the same image. The five-product remote erasure result makes this image a computational stabilizer code, after excluding the case of a common factorization cut. Write it as the span of the labels of an affine three-flat D in the direct sum of the two three-bit alphabets B and C.

Local translations send a point of D to zero. For its direction space V let p and q be the dimensions of its intersections with B and C, respectively, and set k=3−p−q. The quotient of V by the direct sum of these intersections projects isomorphically to each projected space modulo its local intersection. Choose bases of the two local intersections and lift one common basis of that quotient to V. On each party the projected lifts and its intersection basis are independent, so extend to a local basis of the three bits. In these coordinates the flat is
[
 D=\{((u,s,0),(v,s,0)):u\in\mathbb F_2^p,\ v\in\mathbb F_2^q,\ s\in\mathbb F_2^k\}.
]
Every computational affine permutation used here has a target-preserving Clifford lift: its diagonal correction is the ratio of the old and new CCZ signs, a quadratic sign. The lift preserves the coordinate image space. The dimensions p,q are invariants under the labeled product affine group and interchange under the target-preserving exchange of B and C. Hence they classify the flat, including its offset, under these operations.

Let J send the three-bit basis label (u,v,s) to its displayed coordinate pair. This is a Clifford isometry, implemented using zero ancillas and an invertible binary linear change of coordinates. Up to independent nonzero scales the two flattenings are J U and J V for independently chosen three-qubit Cliffords U,V: each maximally entangled stabilizer tensor on A and the three code qubits corresponds to a Clifford unitary by the stabilizer Choi correspondence. In particular, their relative Clifford remains a parameter. Across B and C their local Schmidt ranks are 2^(p+k) and 2^(q+k). For either exception separately, an input-local Clifford undoes its own unitary, leaving p Bell pairs on AB, q on AC, and k GHZ factors. This derivation imposes no joint choice of input basis.

| p | q | k | Schmidt ranks on A,B,C | individual entanglement profile |
|---|---|---|---|---|
| 0 | 0 | 3 | 8,8,8 | three GHZ |
| 0 | 1 | 2 | 8,4,8 | one AC Bell and two GHZ |
| 0 | 2 | 1 | 8,2,8 | two AC Bells and one GHZ |
| 1 | 1 | 1 | 8,4,4 | one AB Bell, one AC Bell and one GHZ |
| 1 | 2 | 0 | 8,2,4 | one AB Bell and two AC Bells |

The omitted (0,3,0) and its exchange factor both exceptions on the same original cut. The all-full terminal result treats (0,0,3). The classification alone does not exclude the other four shapes.
