# Truth-table clause localizers for the odd-charge restriction

Use spin variables s_e = (−1)^{z_e} and reduce modulo s_e²=1. On a connected graph with m≥6 vertices, maximum degree Δ and edge expansion h, let D be a positive integer with 6D<hm. Define moments for |F|≤2D as zero on noncuts and as (−1)^{sum_{v in U} b_v} for F=δ(U), using the smaller side U. Indeed |U|≤2D/h<m/3. These moments have normalization one. Here and below degree is total polynomial degree.

For monomials indexed by A,B of size ≤D set A equivalent to B if A△B is a cut. For three indices in one class, the smaller sides U_AB, U_BC, U_AC satisfy U_AB△U_BC=U_AC: their symmetric difference has empty cut and is either empty or all vertices. The union of the three small sides has size <m. Thus each moment block has entries that factor as products of signs relative to a fixed representative, proving PSD. Consequently the moment functional E is nonnegative on squares of polynomials of degree ≤D.

**Star relation.** Write J=δ({v}) and τ=(−1)^{b_v}. Whenever |F|,|F△J|≤2D,

    E[s_(F△J)] = τ E[s_F].

Noncuts stay noncuts. In the cut case the smaller side U for F has size <m/3, and U△{v} still has size <m/2 because m≥6. It therefore is the chosen smaller side for F△J. This proves the sign relation without a degree allowance for an unreduced multiplication.

**Localizing an inequality.** Let g be a real polynomial function of the bits of a single star J, nonnegative on the allowed parity assignments. Let I_c be the truth-table indicator of a complete assignment c on J. For every real q of degree ≤D−|J| we have

    E[g q²] = Σ_c g(c) E[I_c q²] ≥ 0.

The Boolean quotient has I_c²=I_c, so E[I_c q²]=E[(I_c q)²]≥0 by PSD. A wrong-parity c has s_J I_c=−τ I_c. In the expansion of I_c q², each monomial and its translate by J have support in J together with at most 2 deg(q) other bits, of size at most 2D. The star relation consequently gives E[s_J I_c q²]=τ E[I_c q²], forcing this term to vanish. The identical argument allows arbitrary multipliers p on a vanishing-on-valid-assignments equality when deg(p)+|J|≤2D. Boolean equalities hold exactly by quotient reduction. This argument takes place in the real field.

**Degree cost.** Encode each forbidden full assignment by its usual linear clause inequality, the sum of its mismatch literals minus one being nonnegative. Under the constant restriction from the [expander construction](expander.md), every network factor becomes identically satisfied or becomes one vertex parity on at most Δ edges. For a clause containing a fixed true literal, its restricted inequality is a nonnegative integer constant plus a sum of literal indicators; E[q² times a literal indicator]≥0 whenever deg(q)+1≤D, by idempotence and PSD. If every fixed literal is false, the remaining clause forbids an invalid star assignment in the only nontrivial case. The local argument applies. For a degree-2k SoS refutation using the usual quadratic module (sum-of-squares clause multipliers), deg(q)≤k−1 on each original linear clause. Taking D=k+Δ−1 suffices. Thus no such refutation exists at degree 2k whenever

    6(k+Δ−1) < hm.

The constant substitution preserves degree, and moments of fixed bits lift uniquely. The same bound works for Boolean product equations forbidding individual assignments: a nontrivial restricted clause retains exactly its star of free bits, and the admissible multiplier p has degree ≤2k minus the original equation degree. More generally any single-factor truth-table inequality on a star is covered with an additive Δ allowance. The quadratic-module claim does not assert bounds for proof rules admitting arbitrary uncharged products of input inequalities.

**Degree-charged products of clauses.** For the preordering convention, consider a summand q² times r original linear clause inequalities with 2 deg(q)+r≤2k. After restriction each clause involves at most Δ remaining edge bits (a vertex star, one edge bit, or no free bit). On the union H of these scopes, |H|≤Δr. Decompose the product as its sum over full indicators I_c on H. If any factor is negative, it is a clause from a vertex with an entirely visible wrong-parity star. Translation by this star carries each monomial of I_c q² to another supported in H together with at most 2 deg(q) outside bits, so the same star argument gives zero expectation. All remaining coefficients are nonnegative and the indicator weights are PSD as long as deg(q)+|H|≤D. The degree charge implies deg(q)+Δr≤2kΔ. Thus setting D=2kΔ gives the linear lower bound also for this convention provided 12kΔ<hm. Box axioms or pivot literals with no negative Boolean values obey the same bound. The original charge on products matters even when a restriction turns some individual factors into constants.

[The exact finite checker](check_sos.py) tests star translations, Gram blocks, local indicator weights and two-clause products using rational arithmetic on a 16-vertex graph.
