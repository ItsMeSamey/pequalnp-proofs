# Projective-plane incidence circuits

At order 401, every scalar fan-in-two monotone circuit satisfying the original sparse incidence promise uses at least **646,425 gates**, with arbitrary fanout. This reaches the order-401 target. Two independent readers checked the physical circuit argument. The accompanying Python checker verifies the concluding arithmetic. The official theorem L-meta-2794 asks for every order greater than 100, and its general conclusion remains open. [Order-401 proof](protected-dense-signature-401.md) · [Arithmetic checker](check-protected-dense-signature.py) · [Prior 644,844 bound](iterated-dense-signature.md)

For the original one-sided promise of arbitrary point masks and at most q selected lines, [producer-component extraction](anchored/README.md) and its [combined cost bound](anchored/pruned-cost.md) give s≥4N−O(q) and verify 100s≥Nq through order 396. Here N=q²+q+1. The proof uses stronger tests than correctness restricted to input weight two.

The local lowest-common-ancestor refinement in the [extraction proof](anchored/README.md) extends the verified interval through order 397. At that order it gives 627,678 gates against the 627,288 target.

[Weighted flow through ports](weighted-flow.md) yields s≥4N−1−⌊4N/(q+2)⌋ for the original one-sided promise. This establishes 100s≥Nq through q=399, with three gates to spare at 399. The same estimate falls short at 400.

Along arbitrary projective-plane orders, the same sparse promise gives liminf s(q)/(q²+q+1) ≥ 4.0596. The repeated census proof tracks which original sites and readers survive successive restrictions. [General-order proof](residual-peel-census.md) · [Independent review scope](residual-peel-review.md)

The Lean 4.36 formalization covers plane duality, numerical ledger steps and a growing set of physical restriction and counting lemmas. Independent rebuilds cover 32 physical accounting modules and 19 bilateral construction modules. The construction produces both live programs. Its numerical starting bound still requires two census estimates. The specialization of the posted theorem still assumes the physical lower bound. [Physical formalization and replay receipts](physical-lean/README.md) · [Ledger lemmas](ProtectedIncidenceLedger.lean) · [Plane-duality lemma](IncidencePlaneDual.lean)
