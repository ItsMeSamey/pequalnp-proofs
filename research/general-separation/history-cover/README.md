# Counting with a small shared nonlinear history

The compiler starts with an ordered circuit on original input bits. A vertex cover in the graph of conflicting history columns identifies nonlinear outputs to name. Checkpoints preserve their values across the remaining ordered computation. The bank extension replaces groups of earlier producers by independent linear summaries of their later uses. Each original input has a unique consistent assignment to the auxiliary variables.

The counting bounds depend on the number of named outputs, the ranks of the summaries and the size of the compiled product system. The reference code constructs and checks that system. The faster deterministic counting analysis invokes Theorem 1.4 of Lokshtanov, Paturi, Tamaki, Williams and Yu. The hierarchy application accounts separately for nondeterministic multitape simulation of random-access memory. [Counting argument](grouped-history-product-clock.md) · [Cover and machine model](history-column-cover.md) · [Bank interface](multistage-bank.md) · [Earlier history-rank definition](../temporal-nonlinear-rank.md)

Run `python verify_orders.py` and `python check_bank.py` for the order and bank controls. The fast theorem-based counting backend is outside this reference implementation.

## Implemented quadratic backends

The Gaussian backend accepts systems whose quadratic parts span at most one dimension, together with affine constraints. The character backend accepts a caller-specified bound on the dimension r of that span and evaluates 2^r characters. Inputs exceeding the fragment or budget can be declined. Both reuse the [Gaussian sum](../../direct-sat-algebra/quadratic_image.py) and [affine-domain](../../direct-sat-algebra/quadratic_target.py) implementations. From this directory run `PYTHONPATH=../../direct-sat-algebra python check_gaussian.py` and `PYTHONPATH=../../direct-sat-algebra python check_character.py`. [Gaussian dispatch](gaussian-dispatch.md) · [Character dispatch](character-dispatch.md)
