# Sparse payloads in products of indirect storage access

Let m=2^t, with P=Θ(m/t) pointer rows as in [the ISA tradeoff](isa-sparse-range.md). For payload weight at most H=m^{o(1)}, H≥1, the function has an exact SUM of m^{o(1)} formulas of O(m) leaves, with polylogarithmically many terms for fixed H. A product of fixed r independent copies has m^{o(1)} terms of O(rm) leaves each. In contrast its unrestricted single copy requires Θ(m/log m) terms at that leaf budget.

Choose a power of two q>(H−1)(t−1), 2≤q=O(1+Ht). Give each address j a polynomial f_j over the q-element field whose t coefficients are its address bits. For a target j and a different active address j', their nonzero polynomial difference has at most t−1 roots. Some α therefore separates an active target from all other active addresses. This works inside an interval when the weight bound holds there.

Partition the rows and payload addresses into aligned power-of-two groups. Each row group of size g checks membership of I once. A size-O(g) multiplexer on the low index bits computes each selected pointer bit on demand. For each payload interval J of size c, each α and each field value b, form the bucket of j in J with f_j(α)=b. Check that it contains an active address and every active address in it agrees with the selected pointer on all t bits. For each bit use the corresponding pointer bit to require zero OR on the opposite-bit subbucket. Empty subbuckets give zero. Disjoin over all α and b within the formula.

Any certificate is sound even on dense payloads. On a positive input, if the interval containing the selected address has at most H active bits, a separating α gives a certificate. The row and payload rectangles therefore contribute disjointly. Multiple successful buckets within one rectangle are counted once. Negative inputs need no sparsity promise.

At fixed α the bucket sizes sum to c. Their payload tests cost O(tc+qt) leaves and pointer comparisons cost O(qtg). The total over α is O(qtc+q²t(g+1)+t). For H=m^{o(1)}, choose powers of two c and g of orders m/(qt) and min(P,m/(q²t)). This gives O(m) leaves and O(qt(1+q²)) rectangles. Multiplying r copies' sums uses Boolean conjunction for each product. Thus testing only a fixed product on subpolynomial-weight payloads cannot establish polynomial sparsity lower bounds of positive exponent.

The sparse promise has its own lower bound. Varying payloads of weight at most H gives M_H=sum_{j=0}^{min(H,m)}binomial(m,j) distinct pointer subfunctions per row. The formula skeleton argument in the ISA proof gives S≥Ω(P(log₂ M_H−1)/W). At W=Θ(m) this implies Ω(H) for 1≤H≤m^β and any fixed β<1, with constants depending on β.

An unrestricted product of a growing number of independent ISA instances still has a linear shared circuit. A superpolynomial lower bound there would already separate one language in P from the restricted SUM model. No such lower bound follows from this promise calculation.
