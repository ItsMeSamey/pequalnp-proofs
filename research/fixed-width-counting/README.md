# Two consequences of fixed-width exact counting

Both arguments use the October 25, 2026 manuscript's deterministic exact counting theorem. For fixed clause width k, V variables and encoding length L, write g(V) = V log log V / √log V, with the logarithms truncated at constants for small V. The theorem gives time poly(L) 2^{O_k(g(V))} and polynomial space. The statements below are deductions from that theorem. Publication priority has not been established. [OpenAI manuscript](https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026)

## Counting in a subspace with a quadratic constraint

Let F be a fixed-width CNF on n bits, let S be a nonempty affine subspace of codimension r given by linear equations over the two-element field, and let Q be an explicitly given quadratic polynomial over that field. Define q as the rank of its alternating polar form on the direction space of S. Then the number of x in S satisfying F(x) and Q(x)=1 can be computed deterministically in polynomial space and time

    poly(L) 2^{min(n-r, r+q+O_k(g(n)))}.

Here L includes the affine system and the polynomial. Inconsistent systems are detected by elimination. For linear equations alone the worst-case exponent is at most n/2+O_k(g(n)). The related decision problem is called k-SUB-SAT. [Arvind and Guruswami](https://doi.org/10.4230/LIPIcs.IPEC.2021.5)

**Proof.** Enumerating S gives the first exponent. For the second, compute affine coordinates y on S by elimination. In a suitable basis of its direction space Q takes the form of a sum of q/2 products of disjoint pairs of coordinates plus an affine form. Indeed, choose a pair with polar product one, split off its orthogonal complement and repeat. Once these mixed terms have been removed, the remaining polynomial is affine as a Boolean function. For each product uv the phase (-1)^{uv} equals one half of the sum of the four characters on u,v with respective coefficients +1,+1,+1,-1 in the order 00,01,10,11. Multiplying yields 2^q signed characters with denominator 2^{q/2}. The affine part shifts the character indices and optionally reverses their signs.

Extend each affine character from S to the full space by extending a basis. For r independent equations Ax=b, the indicator of S is 2^{-r} times the sum over r-bit u of the phases (-1)^{u·(Ax-b)}. Multiplying the expansions leaves one ambient character per pair, over 2^{r+q} pairs. Each signed sum on the satisfying assignments of F equals the difference between its counts for the two parity values. A linear chain of at most n XOR gates enforces this parity using clauses of width three with a unique extension. The resulting fixed-width instance uses at most 2n+O(1) variables. Constant characters need no new gates.

The unsigned count uses the same method without Q. Half the unsigned count minus half the signed count gives the answer. All intermediate integer numerators use O(n) bits because there are at most 2^{r+q} terms of magnitude at most 2^n. Generate terms sequentially to preserve polynomial space.

## A lower bound for circuits with fixed-width CNF gates

A circuit contains s ordinary gates of fan-in at most two and h gates that evaluate fixed-width k-CNFs on original inputs and earlier gate outputs. Any number of clauses and any wire fanout are allowed. Repeated clauses can be deleted. For fixed k, the resulting description has polynomial length in n+s+h.

**Counting lemma.** Exact Circuit-SAT takes polynomial space and time

    poly(L) 3^h 2^{O_k(g(n+s))}.

Fix the h proposed macro outputs. Retain variables only for the n inputs and s ordinary gates, and impose ordinary gate relations by width-three constraints. Pin the output to one. For each macro assigned one, include every clause of its predicate, after replacing macro wires by their assigned constants. For each macro assigned zero, its consistency indicator is one minus the indicator of its predicate. Distribute the product of these differences. If f macros are assigned zero there are 2^f terms, and summing over assignments gives 3^h terms. Each term is a fixed-width CNF count with sign. Every accepting input extends uniquely to a consistent assignment of all gates by acyclicity. Sequential summation uses polynomial space and at most O(n+s+h) accumulator bits.

**Lower bound.** The witness language W in E with an NP oracle from the cited quantitative circuit proof satisfies the following. For every fixed k there is a positive constant δ such that for infinitely many input lengths m every circuit computing W at length m has either more than δm macro gates or more than δm√log m/log log m ordinary gates. This is a tradeoff for a specific gate basis. The original source obtains a stronger ordinary-gate bound of order m√log m when every gate has fan-in two. [Published proof used for the reduction](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-circuits.tex)

**Proof.** Use that source's unary H in NTIME(2^n) outside NTIME(2^{n/2}), the clause-index decoder on n+O(log n) bits with O(n) ordinary gates, and its canonical witness W on m=dn input bits for a fixed positive integer d. If the tradeoff failed at all sufficiently large lengths, guess one bounded circuit at length dn and feed the three decoded variable labels into three copies. Accept exactly when no clause is violated. On a yes instance the canonical witness makes the test succeed. On a no instance every candidate assignment violates a clause, including those computed by other guesses. Finite exceptions can be hardwired.

The test uses 3h macro gates, 3s+O(n) ordinary gates, and n+O(log n) inputs. For h at most δdn its counting time has a factor 2^{3δdn log₂3}. For s at most δdn√log(dn)/log log(dn), its remaining exponential factor has exponent O_k(δdn)+o(n), since g is eventually increasing and log(n+3s+O(n)) is asymptotic to log n at the upper bound. Choose δ sufficiently small to put their sum strictly below n/2. Fixed k bounds the canonical description polynomially, so guessing and constructing the test costs polynomial time. The counter thus decides H nondeterministically within the forbidden time bound. A polynomial-space bit-access implementation of the counter can be simulated on a multitape machine with polynomial overhead per access, as in the cited proof.

## Finite checks

Run `python check.py`. It compares signed expansions with exhaustive counts on 350 seeded quadratic examples in affine normal-form coordinates and 100 seeded circuits with nested CNF gates. These tests check the identities on finite samples. The asymptotic bounds follow from the arguments above.
