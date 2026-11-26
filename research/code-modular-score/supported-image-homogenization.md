# Exact supported image and exclusion directions

For binary C on physical edges and a linear score σ:C→V, first
replace V by its attained image and reject T outside it. Let
C0=C∩ker(σ mod T). Each basis t of T requires a homogeneous primal
cycle c_t of C0 with σ(c_t)=t. For each basis λ of T-perp extend
λσ from C to a physical edge covector l. Its restriction to C0 is
zero, hence l belongs to C0-perp. Require a dual lane of C0 whose
class in C0-perp/C-perp equals the class of l. This is a linear
score on the dual lane. Require all cross pairs disjoint. If Y has
image T then l vanishes on C[Y], so l|Y equals the restriction of
some word in C-perp: this is the annihilator identity for shortening.
Their sum gives the required dual lane zero on Y. Conversely take
Y the union of the primal supports. Those rows attain the basis, and
each dual lane zero on Y certifies λσ=0 on all C[Y]. Thus equality,
including every exclusion direction, holds if and only if this
homogeneous portfolio on C0 is attainable. Replacing C0 by C
without the coset conditions would omit exclusions.

Actual prism obstruction. Use row code C=Cut(K3,3) from one nonstar
K4 substitution. Index physical edges by 3i+j, 0≤i,j≤2; row 2 is
the new K4 center. Choose exclusion λ=e01+e10 using only original
prism edges, μ=e02 and target T=span((0,1)) for σ=(λ,μ).
On projecting C0=C∩ker λ away from e00,e01, the seven surviving
columns have parity-check rows 15,54,85 in little-endian masks,
i.e. columns 5,3,7,1,6,2,4. This is F7. The mask Y=78 supports
exactly words 0,78 in C, with latter score (0,1). For m prism
blocks take the sum of all their exclusion scores as ONE λ and μ
from the first copy. The old Y is still a YES witness. Shortening
all other physical blocks gives each local sliced code, so there
are m pairwise-disjoint F7 minor survivor sets of the global C0.
Every strong regularity backdoor has at least m elements. No claim
is made that the coupled sliced code is a direct sum. This controls
a proposed method of applying portfolios, not the complexity of
these particular instances.
