# Full-precision ordinary Cauchy jets of fixed order on parity/COPY inputs

On the physical parity-vertex and edge-COPY networks of the partial-shift control, fix a grid center t and request the coefficients of F(t+2Lz) through z^J modulo 2^P. Keep the original V truncation independent of z. This calculation keeps P arbitrary and accepts an external working-ring character. It does not replace an old lifted negative table entry by minus one.

Use the all-center identity in grid-center-shifts-and-jet-limits.md. Set c=C′(t)/C′(0) and λ=1−2c. In physical row i the linear form is c times its successor edge bit X_s plus Σ_j Δ_ij(z)X_j. Missing successors contribute zero. All Δ have zero constant because the entire c is subtracted at the matching displacement. Equal reads of one physical edge are combined. At each center the slot shift is an injection on its domain. Each edge bit owns two column slots, so at most two rows have that bit as base successor.

Let τ_v be the vertex parity targets, σ_i the external row signs and ρ_j the edge signs. Expand each vertex parity indicator using a spin h_v∈{0,1} and a denominator two. At fixed h set χ_i=σ_i XOR h_{v(i)}. Summing each row bit y_i gives 1−2χ_i(WX)_i since l_0(U)=1−U and l_1(U)=U. Thus 2^v F is the sum of the products of these row factors over h,X, with sign (−1)^(τ·h+ρ·X). This identity holds coefficientwise before modular reduction.

Select rows S whose factor uses a Δ term, selecting one edge j_i in the same packet per marked row. Only |S|≤J can contribute, at every precision. Impose the unary constraint χ_i=1 on each selected row and multiply by ∏_{i∈S}(−2Δ_{i,j_i}(z)). Set all edges in the distinct set Q_S={j_i:i∈S} to one. For a given h let B_j be the ordinary integer sum of χ_i over unselected rows whose base successor is j. Summing out all edge bits gives the following factors:

    j in Q_S       (−1)^ρ_j λ^B_j
    j outside Q_S  1 + (−1)^ρ_j λ^B_j.

The remaining factor (−1)^(τ·h) and the χ pins are unary. Every displayed factor reads at most two vertex spins. Build one graph for this center by joining the owners of the base rows of each edge bit; one or zero incident owners yield unary or constant factors. Removing selected rows deletes incidences only. The graph is measured from the actual supplied slot order and may differ from the original parity graph.

Compute the whole numerator in the original extension coefficient ring at precision P+v, adjoining z modulo z^(J+1). Every output coefficient is divisible by 2^v by the original integral parity-indicator identity. Divide its canonical coefficient representatives by 2^v after summation to recover the exact residues modulo 2^P. Individual terms need not be divisible. No inverse of two is used.

There are at most Σ_{k≤min(2e,J)} binom(2e,k)L^k terms. Each costs input-polynomial work in the numeric parameters P+v, J, L and ring dimension, times at most 2^v by direct evaluation on h. Given a validated tree decomposition of width w of the center graph, binary table elimination replaces the latter factor by 2^(w+1) times a polynomial in the decomposition size. Assign edge and unary factors once to bags that contain their scopes; send a sum over each forgotten spin to the parent. Charge finding/validating the decomposition and processing other centers separately. Direct enumeration streams h and S in polynomial workspace. Bag tables use exponential space in w.

The full constant coefficient is therefore one pairwise partition sum. Any fixed-order jet at full target precision takes polynomial time on supplied bounded-width center graphs, even where the literal Boolean-tie defect expansion has exponentially many nonzero terms in its constant coefficient. The native demand q_t=h_native(u−ν₂(t)) can grow, and widths can vary across centers. This alternative does not establish a general speedup for Hermite recovery.
