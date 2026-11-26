# Why individual long-clause width cannot guarantee an unconditional density improvement

Let G be any explicit CNF on n variables with m polynomial in n, normalized and with at least one nonempty clause. Add t new guard variables and append their positive disjunction to EVERY clause. For the resulting formula F, all nonzero guard words satisfy every clause and the zero guard word recovers G. Hence

    #F = (2^t−1)2^n + #G.

For any fixed width fraction 0<α<1 choose t≥αn/(1−α). This linear-size-in-variables transformation keeps the same clause count and makes every clause have width at least α(n+t). Thus an unrestricted subexponential exact counter for polynomially many clauses, all of linear width, would imply subexponential exact counting for arbitrary polynomial-density CNF. The raw violation probability of each guard-extended clause can be exponentially small; a single exceptional guard assignment retains the whole input count. If a bounded-width short core is allowed, add units forcing all guards false instead. This is a parsimonious counting and satisfiability reduction. The reduction is polynomial-time in the explicit input and uses only linear variable blowup. It is an implication between algorithmic targets, not a computational lower bound.

When no short core is allowed and decision is the objective, an unforced common guard would make every resulting instance satisfiable. For logarithmic padding without a short core, for each original clause C and every word a on t guards include C OR D_a, where D_a is the single width-t guard clause falsified by a. For any guard assignment exactly one copy demands C. This preserves satisfiability and multiplies the count by 2^t. With t=O(log n) the clause count remains polynomial. Conversely, if every clause width exceeds log₂ m then union bounding its uniform violation probability already guarantees satisfiability; that argument alone does not yield the exact count.

**Two-call reduction to exactly uniform width.** Pick W at least the maximum input clause width and introduce W shared fresh variables. Pad each original C to width W by appending W−|C| distinct positive guards, forming F. Let D be the clause on all W positive guards. Then

    #G = #F − #(F AND D).

The second term removes exactly the models with the unique all-zero guard word, on which every padded clause reduces to its original C. Both inputs have n+W variables, exactly uniform width W and clause counts at most m+1. Distinct normalized original clauses remain distinct, and D is a different clause because original clauses are nonempty. Thus every input is a syntactic antichain. W=n gives width exactly half the declared variables; choosing any larger constant W/n gives a uniform fraction as near one as desired. Monotone inputs stay monotone. Empty original clauses and empty formulas are handled separately. This is an exact two-query counting reduction, not a claim that it is hard to decide satisfiability of the padded inputs.

long_uniform_check.py checks the two-count identity and an independent guard-prefix inversion on 1,179 small inputs and width choices.
