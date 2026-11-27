# Local approximation and the cost of checking a short generator projection

Let G:{0,1}^d→{0,1}^m. Choose k=d+ℓ≤m distinct positions J, ℓ≥1, and a local relation R(u,a) on the seed and k-bit projected answer, computed by an existential Boolean circuit with g bounded-fan-in gates. For each u let P(u) be its set of accepted answers. Let η=Pr_u[G(u)_J∉P(u)] and L=E_u|P(u)| for the uniform seed. The test on y asks whether some u and witness accept R(u,y_J). It has the same g existential gates by wiring the named inputs. Its distinguishing advantage between G(U_d) and uniform m bits is at least

    1−η−2^(−ℓ)L.

The generator passes on at least 1−η of seeds and at most 2^d L projected strings can pass on uniform input. This covers partial and multivalued local predictions. Rare ambiguous seeds can still give large L when they permit many projected outputs.

If deterministic approximate coordinate circuits have shared size Q and their error probabilities on the uniform seed sum to η', compare their outputs to y_J using O(k) gates. Then g≤Q+O(k), L=1 and η≤η' without independence. For ℓ=2 and error ≤1/(8k) on every selected coordinate the advantage is at least 5/8.

If SAT on length-M indexed CNFs has deterministic time M^(b+o(1)), b≥1, the same test has a deterministic circuit of size (g+k+2)^(b+o(1)) for growing g+k. Encode the verifier and output condition by O(g+1) bounded-width Tseitin clauses, add unit pins for k observed coordinates, and densely relabel used existential variables (at most two input references per binary gate plus the output). The binary encoding has O((g+k+2)log(g+k+2)) bits. Standard O(T log T) oblivious circuit simulation and hardwiring the topology leave only y_J as input. Raw coordinate positions do not increase a nonuniform gate count. A uniform tester additionally needs a uniform constructor for local circuits and positions and time to read the relevant input.

For example, if every size-B deterministic circuit has distinguishing advantage <5/8 and if SAT has the stipulated clock, no k=d+2 coordinates can jointly have ≤1/(8k) error per seed coordinate with Q+k≤B^(1/(b+η₀)) for any fixed η₀>0 and all sufficiently large B. The same comparison unconditionally holds with an existential distinguisher budget O(Q+k). This tests a proposed local shortcut in a hardness-versus-randomness construction; it does not construct a hard generator. [Nisan and Wigderson](https://www.sciencedirect.com/science/article/pii/S0022000005800431)

Worst-case range hardness alone can coexist with an immediate distinguisher. On seed (x,w) of lengths n,n, define G(x,w)=(x,0^n,V_SAT(x,w)), where the verifier parses x as a conventional bounded-index SAT instance and tests its supplied assignment w, padding or ignoring unused assignment bits. Range membership on (x,0^n,1) is exactly SAT for these encodings. Nevertheless a single middle bit is always zero. Its equality to zero distinguishes the generator from uniform with advantage 1/2. This concerns worst-case verification rather than a circuit lower bound for a generator or its range.

An unrestricted SAT algorithm, a small nonuniform SAT circuit and a fast local generator are distinct hypotheses. A globally polynomial printer in output length may need a large exponent to compute even these selected bits. A small seeded support by itself does not make projected range membership cheap.
