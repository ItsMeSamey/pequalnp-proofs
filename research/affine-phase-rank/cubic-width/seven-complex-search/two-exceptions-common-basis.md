# Two exceptions in the same stabilizer basis on a full-rank cut

Suppose E,F in a seven-list with five block-product rays share one unsigned global Pauli Lagrangian and E has Schmidt rank eight at some original block X. The rays are distinct by minimality. Choose equal-norm gauges so F=(P_X⊗P_R)E for Pauli factors on X and the other two blocks R. In matrix form A for E is a scalar times a Clifford isometry of the three-qubit input onto an eight-dimensional stabilizer code C in R. The matrix for F is B=P_R A P_X^T.

If P_R changes a stabilizer sign of C its image code is orthogonal to C, so A+tB has rank eight for every nonzero t. Otherwise P_R preserves C and acts as a logical Pauli in the Clifford encoding A. Thus B=AQ for an input Pauli Q with at most a fourth-root phase. In the proposed list A+tB has rank at most six because it is a scalar multiple of the rank-one target minus five products. The kernel of I+tQ forces t to be a fourth root of unity in these Pauli gauges. Then E+tF is a stabilizer ray: carry their common stabilizer basis to the computational basis by a Clifford; the two nonzero amplitudes on their affine line have fourth-root relative phase. Their sum would replace two atoms by one, contrary to the unrestricted lower bound of seven.

The conclusion requires a common global stabilizer basis. Equal local-Clifford entanglement profiles alone do not imply it.
