# The triangle and four two-edge paths in the sixteen-flag case

This packet concerns the residual graph consisting of one triangle and four paths of length two. A monotone binary decoder supplied with its 15 incidence flags cannot use twelve OR gates and eight AND gates. The argument concerns arbitrary fanout and is independent of the exploratory searches for small constructive examples.

Start with the residual/interface and path-reader notes in duality/uniform. In degree/t16-cyclic-build, read triangle-ports.md, triangle-readers.md and triangle-no-pure-gate.md. They exclude every triangle-only internal gate and at most one triangle vertex has an AND reader. The earlier cycle count then limits branching triangle flags to one. The normalization and fusion details appear in triangle-unbranched.md.

Next, triangle-no-sibling-product.md eliminates the only way a path center can branch. Its physical ten-input host transfer and remote charges can also be read in triangle-no-unbranched.md. The joint budget in triangle-ordinary-budget.md forces a single exceptional path-center AND hot on one singleton and a single-read triangle vertex at an AND. The unique extra terminal and the simultaneous two-raw specialization in triangle-final-two-deletions.md finish the contradiction. The separate full no-branch case analysis is not needed for this last count: the upper bound of one branching vertex guarantees at least one single-read triangle OR, and the budget subsequently forces exactly one of each reader type.

## Previously established dependencies

The finite physical minima used here are size 27 at eleven inputs, size 24 at ten inputs, and size 21 with exactly four AND gates at nine inputs. The OR bound for threshold two is 2n−4. The proof also invokes the earlier seven-AND ten-input raw regularity and pure-triple lemma, and the independent-raw OR increment. The relevant mathematical notes preserve their source paths. The historical triangle-plus-P5 decoder lower bound is one input to the path-flag fusion lemma; its metadata and checked log are included. This package does not re-run earlier synthesis or DRAT verifiers and does not reproduce all historical source artifacts.

The square-plus-three-paths-and-one-edge residual is outside this packet. Mathematical review receipts are kept separately by the publication coordinator.
