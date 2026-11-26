# Hamming-support correction rank over any field

The manuscript's auxiliary construction seeks M with M[u,y]=0 when the variable schedule a_y and factor schedule d_u disagree at more than R−1 positions. The measurements C must satisfy ker C⊆ker(I−M), hence rank C≥rank(I−M). No coefficient restriction or symmetry is needed below.

For an orbit of h active unequal pairs under independent coordinate swaps, encode a label by its h orientation bits. Within the orbit dist(a_y,d_u)=h−dist(u,y). Thus on the principal subset of orientations of weight at most floor((h−R)/2), the support requirement forces M to vanish identically. The corresponding submatrix of I−M is an identity, giving rank at least the size of that Hamming ball. For M that preserves each orbit, sum this obstruction over orbits. Without orbit preservation a single restriction is still valid.

The full catalogue gives a normalized bound even when M mixes orbits. Mark floor(r/2) of the r colors. Let H count marked symbols in a word, p=floor(r/2)/r and μ=Qp. Take all u=(a,d) with H(a)≤μ−R/2−1 and H(d)≥μ+R/2+1. For any u,y in this set, H(d_u)−H(a_y)>R−1, so the requisite Hamming distance is too large and M[u,y]=0. Therefore normalized correction rank is at least

    Pr[Bin(Q,p) ≤ μ−R/2−1] · Pr[Bin(Q,p) ≥ μ+R/2+1].

Here 1/3≤p≤1/2 for every r≥2. For R=o(Q) each tail is at least c exp(−C R²/Q), by summing order-√Q near-threshold atoms and using Stirling's binomial estimate, with constants uniform in p. This recovers the exponential scale of the exceptional-weight bound. It applies to the full-catalogue correction model in all characteristics, including arbitrary replacement matrices obeying its support condition. The layout-determinant.md argument covers more general layouts and loses a factor of order √Q.
