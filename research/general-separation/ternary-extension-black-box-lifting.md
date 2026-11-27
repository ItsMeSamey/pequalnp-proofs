# Exponentially many ternary probes can be required for one extension-field value

Fix any ω∈F₉∖F₃. The input is an evaluation oracle for an unknown n-variate multilinear polynomial P over F₃. Its promise is that it arises by pinning auxiliary variables of the full multilinear extension of a positive CNF of width at most two, with every variable in exactly two distinct clauses. Queries give P(a) for a∈F₃ⁿ. For this promise alone, distinguishing P(ω,…,ω)=0 from P(ω,…,ω)≠0 requires at least (3/2)^n queries in the deterministic worst case. Any randomized algorithm correct on every oracle with probability ≥1−δ, 0≤δ<1/2, needs at least (1−2δ)(3/2)^n expected queries on the zero oracle. This includes the problem of computing the exact field value. The target point and the family construction may be public.

## Pinned positive formulas

For each c∈F₃ use a private gadget on one surviving symbol x; never reuse a private symbol between gadgets. Over the Boolean cube the positive OR of x,u has multilinear representative x+u−xu. The positive formula (x∨y)∧(y∨z) has representative y+(1−y)xz: for y=1 it is true and for y=0 it is xz. These are formal identities for the unique multilinear extensions, so their pinned polynomials extend over F₉. Use

| Missing ternary value c | Formula and pins | Resulting polynomial f_c(X) |
|---|---|---|
| 0 | unit clause x | X |
| 1 | (x∨y)∧(y∨z), y=z=2 | 2+X |
| 2 | x∨u, u=2 | 2−X |

Each has just the root c, and each f_c(ω) is nonzero. Conjoining n independent gadgets multiplies their polynomials formally, since the product has disjoint variable supports and agrees on the Boolean cube. Thus every vector c gives the oracle P_c(X)=∏ᵢ f_{c_i}(X_i). Multiply by an additional independent unit clause b, with b pinned to 1 on the nonzero family and 0 to realize the identically zero oracle. This switch is fixed inside the oracle, not available as a query coordinate.

For every old variable v that appears just once, introduce a distinct private g_v and add (v∨g_v) and the unit clause (g_v); pin g_v=1. This gives v and g_v each exactly two distinct clause incidences, and changes no other incidence. It applies to all the surviving inputs, private variables and b when needed. Width remains at most two. To verify preservation, specialize these guards first at Boolean one in the multilinear representative. Across all Boolean assignments to the other variables the added clauses are then true. Multilinear uniqueness in the remaining variables therefore gives an identity of formal polynomials. Only afterwards make the possibly non-Boolean ternary pins shown above. This order of proof avoids treating repeated occurrences of v as independent during arithmetization.

## Adaptivity and randomness

Draw the missing values c_i independently and uniformly in F₃. For every fixed a∈F₃ⁿ,

    Pr_c[P_c(a)≠0] = Pr_c[∀i, c_i≠a_i] = (2/3)^n.

For a deterministic algorithm list the queries it makes when every reply is zero. Until the first nonzero, its adaptive execution on P_c follows exactly that list. The probability a list of length q contains a nonzero reply is at most q(2/3)^n, by the union bound even for repeated or correlated queries. If this is less than one, some P_c produces the entire zero transcript, although its target value is nonzero. An always-correct deterministic algorithm must therefore reach the stated lower bound on its zero execution.

For a randomized algorithm couple runs on the zero oracle and on P_c using the same coins. Fixing the coins fixes the list of queries on the zero oracle, independently of c. If that list has length Q₀, the probability over c of different transcripts or different output is at most min(1,Q₀(2/3)^n). Average over the coins. An infinite expected query count on zero already implies the bound. With finite expected query count it issues finitely many queries almost surely. If a run loops between queries, count this as failure. Under the coupling with no hit both executions have identical behavior, including any nontermination. On zero, the probability of declaring a nonzero extension value is at most δ. Averaged over the nonzero family, the probability of that same declaration is at least 1−δ. This difference is at most the coupling's disagreement probability, hence

    E[Q₀] ≥ (1−2δ)(3/2)^n.

Equivalently under the equal mixture of the zero oracle and the random product oracle, a q-query algorithm has average success at most 1/2+q(2/3)^n/2. The proof permits arbitrary adaptive ternary probes and unbounded computation between probes. Its oracle supplies the *pinned resultant function* only. Access to the original formula, the pins, a circuit description, symbolic derivatives, extension points or auxiliary variables is a different model. In the explicit product-and-pin presentation the target is computable by n field multiplications and inspection of the switch. The lower bound coexists with the [polynomial-time ternary numerical evaluation theorem](positive-read-two-ternary-evaluation.md) and makes no assertion about the complexity of white-box extension-field evaluation on arbitrary positive read-two CNFs.
