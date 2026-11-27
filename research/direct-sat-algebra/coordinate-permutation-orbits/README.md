# Two coordinate permutations and a set of zero pins

Given two explicit permutations of D coordinates and a starting bit vector, decide whether some vector in its orbit is zero at every prescribed coordinate. The [reduction and certificate](projection-pin-orbits.md) establish NP-completeness and explain how to recover witnesses. Group elements can be certified by straight-line programs of polynomial length.

The [two- and four-position result](four-color-orbit-boundary.md) gives a polynomial solver for the specified pair-block action and a four-coloring reduction on four-position blocks. Three-position blocks already give NP-completeness when the conjugate involutions need not commute. The [ternary solver](ternary-orbit-kernel.md) enumerates a translation kernel of dimension r in time 3^r times a polynomial. Its default rank cap is 10; a cap result is inconclusive. Use `rank_cap=None` for the complete algorithm on its stated input class.

Two lower bounds concern the original physical orbit coordinates. [The polynomial-calculus transfer](orbit-pc-degree.md) gives degree Ω(√D) over the binary field on a family of four-position inputs. [The affine-leaf DNNF theorem](orbit-affine-dnnf.md) gives size 2^Ω(√D) to represent the exact pinned solution set on a separate family, even allowing existential auxiliary coordinates. Feasibility on that latter family is immediate.

Run `python check_orbit_subcube.py`, `python four_color_orbit.py`, `python pair-orbit-solver.py`, `python orbit-affine-obstruction.py` and `python check_ternary_kernel.py` using the Python standard library. The checks include orbit sizes, original witness lifts, subgroup ranks and straight-line-program replay.

## Recognized four-color inputs

A [matroid algorithm](physical-bdd-union/orbit-rado-kernel.md) contracts an affine subsystem and enumerates independent components of a maximum-deficiency core. The [modal-fiber algorithm](orbit-color-frontier/modal-fibers.md) can certify groups of vertices whose contraction preserves a witness. Their costs depend on the recognized structure. On the connected K5-plus-path controls the matroid solver took 256 assignments on NO and one on SAT; direct four-color search used 64 and six to eight respectively. An independent cycle-based solver also handled those controls.

With this directory on the Python module path, run `PYTHONPATH=. python physical-bdd-union/check_rado.py`, `PYTHONPATH=. python orbit-color-frontier/check_modal_fibers.py` and `PYTHONPATH=. python orbit-color-frontier/check_modal_kneser.py`. Satisfying outputs are checked through the original coordinate permutations.
