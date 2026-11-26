# Exact certificate ceiling for matrix-valued Boolean gate tests

Let Ω⊆{0,1}^n be any nonempty promise and let b∈Ω. Add and multiply Boolean functions on Ω pointwise over the binary field. A matrix-valued map H is additive, unital, and pinned at the inputs when H(1)=I and H(x_i)=b_i I. Its values may be noncommuting. Write δ(a,g)=H(ag)−H(a)H(g) for its multiplication defect.

**Exact certificate price.** Among identities f+f(b)=∑_{j=1}^t ℓ_j g_j with zero-at-b coordinate literals ℓ_j=x_{i_j}+b_{i_j} and unrestricted Boolean functions g_j on Ω, the smallest t is the ordinary certificate complexity C(f,b). Indeed, any point on which all these literals vanish agrees with f(b), so their coordinates form a certificate. Conversely take a minimum certificate in any order. The choices

\[
g_j=(f+f(b))\prod_{a<j}(1+\ell_a)
\]

partition the disagreement set by the first violated certificate coordinate. If f has a size-s Boolean circuit, each g_j has a circuit of size s+O(t) using the same input pins. Replacing the coordinate literals by arbitrary zero-at-b affine forms gives precisely the smallest codimension of an ambient affine flat through b on whose intersection with Ω the output is constant.

Applying H to the identity gives

\[
H(f)-f(b)I=\sum_j \delta(\ell_j,g_j).
\]

Thus the rank of the left side is at most the sum of the t defect ranks, including for normalized rank or expected rank. An arbitrary subadditive matrix seminorm gives the same inequality. This requires no test on general products and no matrix-dimension factor. For positive CLIQUE_{v,k} inputs the edges of a witness give t≤C(k,2). For a positive N-cycle on the row-one-hot promise with N≥2, every one of the N rows must occur in any coordinate certificate: changing an unconstrained row alone can destroy bijectivity. One positive pin per row suffices, giving t=N.

**OR nearly attains the ceiling.** For n≥2, b=0, take a diagonal matrix indexed by unordered pairs i<j. Its diagonal entry at (i,j) is f(e_i)+f(e_j)+f(e_i+e_j). This H is additive, sends 1 to I, and sends every input coordinate to zero. It sends OR_n to I, whereas OR_n(b)=0. For every coordinate k and every g, δ(x_k,g) can be nonzero only on pairs containing k. Its normalized rank is at most 2/n, attained by taking g to indicate the point e_k. The ratio for OR is therefore n/2 even though OR has a linear-size ordinary circuit.

**How conditional row selection changes the price.** Set D=2^n−n−1 and index D rows by S⊆[n] of size at least two, with n≥2. Together with 1 and the coordinate functions, OR_S form a basis for all functions on the full cube. In the squarefree normal form OR_S has coefficient one on the monomial S and has only subsets of S below it. Let v_f be the D-vector of coefficients of f on these nonlinear basis elements. For any D chosen points b_j define E_f=diag_j(f(b_j)), let u be the all-ones column, and define

\[
H(f)=E_f+u v_f^{\mathsf T}.
\]

Here the pins are the diagonal coordinate matrices E_{x_i}, permitting different baselines in different rows. The map remains additive and unital. For every fixed pair f,g the image of H(fg)−H(f)H(g) lies in span(u,E_fu), as follows by multiplying the two matrices and using E_fE_g=E_{fg}. Every individual product defect thus has rank at most two.

Now restrict one OR_n circuit differently in each row S by setting every input outside S to zero. Its row-specific outputs are f_S=OR_S. Patching together row S of H(f_S)−E_{f_S} gives the identity matrix: v_{f_S} is the S-th coordinate vector. The patched rank D is exponential even though the original circuit uses only n−1 AND gates and free affine operations. The individual tests involve fixed function pairs, while the patched quantity selects a different residual function at each row. A bound for the latter requires an explicit compatibility condition on those jointly induced operand tuples.
