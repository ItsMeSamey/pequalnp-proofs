# No rank-three weighted pair of full three-qubit stabilizer encoders

If rank(aU+bV)=3 for nonzero a,b and full stabilizer isometries U,V, their eight-dimensional stabilizer images intersect on at least five dimensions and hence coincide. The relative Clifford C has, after a phase adjustment, eigenvalue 1 of multiplicity exactly five. We exclude this.

The trace has magnitude ≥2. The Pauli coefficients of C are its normalized stabilizer Choi state's Bell-basis coordinates, flat on affine support. The identity occurs, so the support W is linear with dimension ≤4. Symplectic basis extension and Clifford conjugation put W into full Pauli labels on s qubits and Z labels on t others, with 2s+t=dim W. Odd multiplicity requires no idle qubit, s+t=3, leaving (s,t)=(0,3) or (1,2).

In the diagonal case, align the phase at a unit eigenvalue. The parity distinguishing nonreal entries of the diagonal Clifford is affine, so five unit entries force all entries real. Its Boolean sign exponent is quadratic, whose weight on three bits is even (zero full-cubic coefficient). Exactly five unit entries are impossible.

In the other case C preserves two control bits z and acts on the remaining qubit by C_z. Five unit eigenvalues require one C_z=I; shift this label to 00. Conjugating either control X by C gives a Pauli with unchanged control shift, so C_{z+e_j}C_z† is a fixed data Pauli up to scalar. Consequently C_z=i^{f(z)} X^{u(z)}Z^{v(z)} with u,v binary linear. Removing these controlled X,Z gates in fixed order leaves a diagonal Clifford on the control bits, with f mod two linear since C_00=I. A block's spectrum is real iff f(z)+u(z)v(z)=0 mod two. Each real nonscalar block contributes one unit eigenvalue. Nonreal blocks contribute zero, and any real scalar block contributes zero or two.

Independent u,v yield only one scalar block and at most three real blocks (a nonzero quadratic term cannot vanish everywhere). Thus at most four unit eigenvalues occur. Dependent u,v give affine realness with either two or four real blocks since 00 is real. Two allow at most four unit eigenvalues. For four, the even number of scalar blocks (two or four) gives even total unit multiplicity. This proves the impossibility of five.

Combining with full-pair-low-rank-collapse.md, every weighted full pair of rank≤3 merges to zero or one stabilizer Choi ray. Thus any seven-list component with two full parents and remainder of aggregate rank ≤2 is excluded, including the entire (8,8,2) triangle. The obstruction applies on every original cut.

The pair cutoff is sharp: let U=I and V be the diagonal Clifford with signs (−1)^{z+xy}. Then I−V has rank four and its Choi support is the diagonal copy of the four nonaffine graph points z=1+xy, so it is not one stabilizer ray. A common stabilizer isometric embedding allows larger remote registers. This example does not give a seven-term G3 representation.
