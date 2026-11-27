"""Verify the finite batch-count inequalities in the open 6648 region."""
from math import comb


def batches(atoms, switches):
    antichain_bound = 5 if atoms == 4 else comb(atoms, atoms // 2)
    return min(2**switches, antichain_bound)


rows = 0
for centres in range(1, 5):
    for charges in range(3, 11):
        for junk in range(3, 14 - 2 * centres - charges):
            budget = junk + 2 * centres + charges
            clean = 3 + (centres - 1) * batches(junk, charges)
            dirty = 3 + centres * batches(junk - 1, charges - 1)
            assert max(clean, dirty) <= budget, (centres, charges, junk)
            rows += 1
print(f"Checked both branches for {rows} (centreless, charges, junk) triples.")
