# Counting the original padded planar formula

The solver recognizes the signed clause pattern and counts its satisfying assignments by exact planar perfect-matching arithmetic. The mathematical analysis connects this source count to the selected final scalar for the given layout. Intermediate trial queries have different requirements.

Run `python -B check_padded_planar_solver.py` from this directory with NetworkX installed. The frozen independent checker also uses the shared workspace lock at `/workspace/scratch/pnp-native-search.lock`. Its recorded controls used NetworkX 3.7. They include the shuffled triangle, checked over all 2^21 original assignments, with 321,048 satisfying assignments. The arbitrary-pin and signed-interpolation extensions are proof documents.

The matching enumerator computes the normalized residue of the pinned scalar divided by 2 raised to the kernel dimension. For a raw residue modulo 2^q, it returns zero when q is at most the dimension. Otherwise it computes the normalized residue at precision q minus the dimension and restores that factor. The tree-layout lower bound applies to the open predicate. The separate scalar calculation can still evaluate a fully pinned query exactly.
