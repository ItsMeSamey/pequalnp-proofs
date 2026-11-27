# A Fibonacci coefficient in a fixed dictionary for independent lookup

Fix a constant number of banks r≥2, m=2^k payload bits per bank and a power-of-two number P=Θ(m/log m) of pointer words per bank. Bank a has its own primary index I_a, words p^a_i and payload y^a. The full-cube target is the product of the selected bits. Its input length N is Θ(rm). There is a polynomial dictionary of O(N)-leaf Boolean formulas in which every real linear combination approximating this target to uniform additive error 1/5 needs an exponentially large aggregate coefficient on one specified feature. Adding one O(N)-leaf formula gives an exact representation with all active coefficients one. Here a dictionary coefficient aggregates all repetitions of that feature.

## Constructing the dictionary

For each primary tuple α let H_α test that all primary indices match α and all addressed payload bits on those rows are one. Each bank uses a binary multiplexer tree of O(m) leaves and an O(log P)-leaf index guard. The H_α have disjoint supports and sum to the target.

Take t=m and distinguish the all-zero primary tuple. On this rectangle the unused pointer word p¹₁ gives a tag u in 1,…,t by interpreting its binary value and adding one. Every tag occurs on a YES input, for example with the payloads fixed to all ones. Keep the other H_α. Replace H₀ by t formulas D_j=H₀ A_{u,j}, where A_{u,j}=1 exactly when u=j or when j<u and u−j is odd. Equality and comparison to fixed constants use O(log t) leaves, as does their Boolean combination with the low bit for parity. Comparisons can use the binary encoding of u−1 and adjusted constants. The resulting explicit dictionary has P^r−1+t members. Each has O(N) leaves. Taking m→∞ makes t=Θ(N) for fixed r.

## Forced coefficients and approximation

On one YES input for each tag the dictionary response is the unit lower triangular matrix A, together with zero columns for the other rectangles. Exact equality forces Ac=1. These equations also suffice on the entire distinguished rectangle because H₀ vanishes on its NO inputs. With F₀=0, F₁=1 denoting Fibonacci numbers, forward substitution gives c₁=1 and c_i=(−1)^{i+1}F_{i−2} for i≥2. Indeed c₂=0, c₃=1, and subtracting the row equation at i−2 from that at i gives c_i=c_{i−2}−c_{i−1} for i≥3. All other rectangles have coefficient one in the resulting full-cube representation.

For the approximate case take z solving Aᵀz=e_t. Backward substitution gives z_t=1 and z_{t−k}=(−1)^k F_k for 1≤k<t. The first two backward steps give −1 and 1, and the subsequent magnitudes satisfy the Fibonacci recurrence. Thus ||z||₁=F_{t+1}, and zᵀ1=c_t. If the full-cube uniform error is ε and the coefficient on D_t is v_t, restriction to the chosen YES inputs gives

    |v_t − c_t| ≤ ε F_{t+1}.

At ε=1/5 this forces |v_t|≥F_{t−2}−F_{t+1}/5 for t≥2. Since F_{t−2}/F_{t+1} tends to φ⁻³>1/5, where φ=(1+√5)/2, the required magnitude is Ω(φ^t). Repetitions with separately bounded weights must supply that aggregate magnitude. The stated theorem uses exactly the displayed dictionary with no free intercept.

## Restoring one feature

Adding H₀ restores the exact unit-coefficient sum of the H_α on every input. The large coefficient and the signed test z therefore witness conditioning of this specified dictionary. Both witnesses depend on which near-linear features are available.

The checker exhausts a two-bank instance on 1,024 full inputs, verifies the restoration, and checks the triangular identities at t=30. For that matrix the exact coefficient is −317811, the dual norm is 1346269, and error 1/5 forces magnitude at least 242786/5. [Executable checker](isa_conditioned_dictionary_check.py)
