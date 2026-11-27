# Counting with a small shared nonlinear history

The compiler starts with an ordered circuit on original input bits. A vertex cover in the graph of conflicting history columns identifies nonlinear outputs to name. Checkpoints preserve their values across the remaining ordered computation. The bank extension replaces groups of earlier producers by independent linear summaries of their later uses. Each original input has a unique consistent assignment to the auxiliary variables.

The counting bounds depend on the number of named outputs, the ranks of the summaries and the size of the compiled product system. The reference code constructs and checks that system. The faster deterministic counting analysis invokes Theorem 1.4 of Lokshtanov, Paturi, Tamaki, Williams and Yu. The hierarchy application accounts separately for nondeterministic multitape simulation of random-access memory. [Counting argument](grouped-history-product-clock.md) · [Cover and machine model](history-column-cover.md) · [Bank interface](multistage-bank.md) · [Earlier history-rank definition](../temporal-nonlinear-rank.md)

Run `python verify_orders.py` and `python check_bank.py` for the order and bank controls. The fast theorem-based counting backend is outside this reference implementation.

## Implemented quadratic backends

The Gaussian backend accepts systems whose quadratic parts span at most one dimension, together with affine constraints. The character backend accepts a caller-specified bound on the dimension r of that span and evaluates 2^r characters. Inputs exceeding the fragment or budget can be declined. Both reuse the [Gaussian sum](../../direct-sat-algebra/quadratic_image.py) and [affine-domain](../../direct-sat-algebra/quadratic_target.py) implementations. From this directory run `PYTHONPATH=../../direct-sat-algebra python check_gaussian.py` and `PYTHONPATH=../../direct-sat-algebra python check_character.py`. [Gaussian dispatch](gaussian-dispatch.md) · [Character dispatch](character-dispatch.md)

## Complete SAT decision on original inputs

Use `cnf_routes.solve_cnf(n, clauses)` for clauses of width at most three, with signed, one-based integer literals. It returns a witness mask or None, plus the route used. The structural tests solve 2CNF, use bounded tables for a certified elimination order, or search for a small set of variables meeting all remaining ternary clauses. The circuit solver tries sparse substitution and bounded-rank quadratic counting before enumerating the remaining input coordinates. The exhaustive fallback can take exponential time. Successful witnesses are checked against the original clauses. [Circuit algorithm](complete-portfolio.md) · [3CNF routes and examples](structural-cnf.md)

The representation bound concerns encodings whose number of extensions has the correct parity on each raw input. For independent sets of an n-vertex path, any such affine-plus-quadratic encoding has 2r−h at least n, except when n is 1 modulo 3, when it is at least n−1. Here r is the rank of the quadratic parts and h is the number of free auxiliary bits after affine elimination. The path decision problem itself is easy. [Proof](complete-portfolio.md)

Run `PYTHONPATH=../../direct-sat-algebra python check_complete.py` and `PYTHONPATH=../../direct-sat-algebra python check_routes.py` to reproduce the original-input checks.
