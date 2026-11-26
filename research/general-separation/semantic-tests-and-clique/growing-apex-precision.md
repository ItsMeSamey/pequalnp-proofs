# Growing apex number and high-precision separator width

Let B(M) be a positive integer proxy asymptotic to sqrt(loglog M), formed from binary integer lengths and integer square root. For a graph with a supplied planar deletion set of size t put b=ceil(log₂(t+2)). For sufficiently small absolute dyadic c,γ>0 allow

    b ≤ 2+γ B(M),      graph size ≤ M max(1,ceil(c B(M)/b)).

Use the [component lookup or pair-connectivity atoms](apex-switch-component-tables.md), and check these conditions on each guessed atom. For each fixed d some L_d in NP lacks at infinitely many lengths M an exact real SUM of ≤M^d atoms in the mixed theorem enlarged by these growing-apex atoms at their individual budgets. In particular near-linear graph size is permitted with exp(Ω(sqrt(loglog M))) designated apices for a small constant in the exponent.

The slot selection uses heavy threshold L=ceil(CK) per atom for its own density K. The failure bound depends on K/L. Each projected graph has q=O(n+nL) live edges and at most 2q ordinary vertices after offsets. Enumerate its distinguished-vertex partitions; across at most four factors the overhead is at most a constant times Bell(t_max+1)^4, allowing the optional extra terminal apex. With M≤2^{O(n)}, t_max log(t_max+2)=2^{O(sqrt(log n))}=n^{o(1)}, so the enumeration costs 2^{o(n)} time and polynomial ambient space.

For each partition use b+O(1) bits per tag incidence. Equality, validity and forced-name tests have O(b) bits and polynomial-time entries. The orientation-transfer index and local monomial choices have bounded size, since the tag merely selects the applicable matrix. The signed coefficients have O(b) bits per local factor; split the partition prefactor into ≤t factors U−j for an adder tree with O(q+t) inputs of bounded width. The lookup vertex has O(log(q+t+2)) ports. Its residual values can be precomputed in polynomial ambient time. Thus the wire budget is O((q+t+1)(b+1)), with valid source degree and entry bounds. Distribute partition and two-terminal terms, sum modulo 2^{N+1} across the alternatives for the same product and parity bucket, then decode. Intermediate terms may be signed; the completed per-input product is Boolean.

Since Kb≤cB(M)+O(b), the new sparse wire part is O((C+1)(c+γ)n sqrt(log n)+n+t(b+1)). Other factors and the dense term obey their existing bounds. Choose δ,C as in the [mixed proof](mixed-dense-sparse-tensors.md), then c,γ small enough for the combined contractions, and finally ε depending on d. The new exponent cost is O((C+1)(c+γ)n)+o(n). Ordinary polynomial-size circuits evaluate the atoms. The hierarchy conclusion concerns these restricted representations.

## Unrestricted partition interfaces

For t≥1 let C[π,σ]=[π∨σ has one block] on all t-terminal partitions. Each partition is realizable by a terminal forest, and C is connectivity after gluing. Write Z[π,ρ]=[π≤ρ] for refinement. Z is integer unimodular in a linear extension. By partition-lattice Möbius inversion,

    C=Z D Zᵀ,     D[ρ,ρ]=(−1)^{j−1}(j−1)!   for j blocks in ρ.

This classical factorization yields integer Smith factors (j−1)! with Stirling multiplicities S(t,j), after sorting by j and changing signs. [Burgos](https://arxiv.org/abs/1603.06428) · [Bodlaender et al., binary cut matrix](https://arxiv.org/abs/1211.1505) · [Freedman, Lovász and Schrijver](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2004-41.pdf)

Over R=Z/2^p the minimum d allowing C=UV via R^d equals the sum of S(t,j) over j with ν₂((j−1)!)<p. The diagonal gives the upper bound. Its image is the direct sum of this many nonzero cyclic ideals and requires this many generators by reducing the image module modulo twice itself. In a factorization through R^d the intermediate image is a submodule of R^d with at most d generators by Smith reduction over this principal ideal ring. Its image under U also has at most d generators. Thus this is inner factorization rank, including nonunit entries, not just rank after reduction modulo two.

For p=1 the value is 2^{t−1}. For p>ν₂((t−1)!), in particular p≥t, it is Bell(t). A universal gluing-compatible network interface with h Boolean wires has at most 2^h intermediate states, so at high precision it needs h≥log₂ Bell(t)=Ω(t log t) on arbitrary terminal partitions. This applies to the shared local interface, with global reorganization of the input graph outside its scope.
