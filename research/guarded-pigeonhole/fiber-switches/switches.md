# Exact symmetric adjacency switches before a chart change

Delete coordinates forced zero on Lx=z and row-reduce L. The alternating matrices A' with identical individual guard values to A for all x on this nonempty affine fiber are exactly A'=A+LᵀHL+diag(LᵀHz), for symmetric H with diag(H)=Hz. Here diag applied to a matrix extracts its diagonal and applied to a vector forms a diagonal matrix.

For R=A+A', the row R_i annihilates the nonempty slice Lx=z,x_i=1. Thus R_i=α_i L+β_i e_iᵀ with β_i=α_i z. This includes coordinates forced one. Stack the α_i in C. Then R=CL+diag(Cz), so CL is symmetric. For any right inverse J of L, C=LᵀCᵀJ=LᵀH and H=JᵀCLJ is symmetric. The diagonal condition gives Lᵀ(diag(H)+Hz)=0; use full row rank. Conversely (Rx)_i=(LᵀHz)_i(1+x_i) on the fiber, so the individual guard differences are zero.

With nonzero target use marker basis z=e_t. Choose all off-diagonal entries and H_tt, then H_ii=H_it for i<t. This gives 16 candidate H at t=3 (8 for zero target); different H can yield the same switched adjacency. A switch acts on each pair by an affine shear y_i↦y_i+b_i(1+x_i) on the fiber. Consequently arbitrary interleavings with ordinary marked local complementations are covered by the completion theorem in README.md.

On the 5-cycle 0,1,2,3,4 choose marker columns (1,1,0),(1,0,1),(1,0,0),(0,1,0),(0,0,1), target (1,1,1). No coordinate is fixed. H=e₁e₁ᵀ complements the triangle on {0,1,2}, turning the 5-cycle into the bipartite 4-cycle on {0,2,3,4} and an isolated vertex. Some switched edges can have both endpoints selected. The original 5-cycle alone has no ordinary locally bipartite chart, as shown by the odd triangle-free-edge test. This makes the marker-aware recognition strictly stronger.
