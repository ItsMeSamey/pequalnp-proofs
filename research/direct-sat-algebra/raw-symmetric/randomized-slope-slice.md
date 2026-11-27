# A one-sided weighted test for arbitrary frozen syndrome matrices

The input is an independent binary row basis for H and an evaluator u↦D(u), with no affine or symmetry requirement on that evaluator. For fixed u let Sᵤ consist of binary controls t with Ht=u for which D(u)+diag(t) is invertible. Its squarefree enumerator over K is

    Pᵤ(X) = Σ_{t∈Sᵤ} ∏_{j:tⱼ=1} Xⱼ.

Distinct controls give distinct monomials, so Pᵤ is nonzero exactly when Sᵤ is nonempty. Its total degree is at most n. With independently uniform αⱼ in a field of size q≥2n, a nonempty fiber gives a nonzero evaluation with probability at least 1−n/q, by Schwartz–Zippel. This remains true for even-sized fibers. No independence among different syndrome evaluations is required: for global success bound failure using any one nonempty fiber.

Evaluate over K[F₂ʷ], writing Hⱼ for a column of H. For bit zero column j contributes Dⱼ; for bit one it contributes αⱼ z^(Hⱼ)(Dⱼ+eⱼ). Sum the two columns for a free bit or use the corresponding single column for a pin. By determinant multilinearity the coefficient at zᵘ is exactly the weighted enumeration for that prefix. Once the root evaluation is nonzero, retain the same α throughout: the two child evaluations sum to the parent, so if the zero child vanishes the one child is nonzero. At the final control the implementation checks Ht=u and full binary rank. The optional target wrapper solves and replays the leaf equation. Unsuccessful tests return INCONCLUSIVE, without a nonexistence claim. Repeating independent trials R times bounds the miss probability by (n/q)^R for nonempty requested search spaces.

The extension uses a verified polynomial modulus of degree O(log(n+2)). Each group-algebra product has polynomially many component products in F₂[F₂ʷ], computed via the integer Walsh backend, followed by reduction modulo the field polynomial. Division-free Berkowitz costs polynomially many products for each tested prefix. Per trial the single-fiber bit-time bound is O*(2^w); the all-fiber bound is O*(4^w), plus the cost of evaluating D. Working space is O*(2^w). The code draws fresh weights from system randomness by default and accepts an explicit generator for reproducible tests.

Direct enumeration agreed with all 1,488 sampled weighted prefix evaluations. Fixtures included nine nonempty even fibers and 47 asymmetric frozen matrices. Both selected controls and target witnesses were checked independently.
