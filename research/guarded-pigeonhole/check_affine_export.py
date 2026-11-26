"""Compute exact affine-export ranks on the two-switch test instance."""
from check_unit_restrictions import bit, rows

def rank(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            lead = max(vector)
            if lead not in pivots:
                pivots[lead] = vector.copy()
                break
            vector ^= pivots[lead]
    return len(pivots)

def image(k):
    return {0,bit(12)} if k == 13 else {bit(k)}

polynomials = []
for pivot,mask,offset in rows[:-1]:
    affine = {0} if offset else set()
    for k in range(34):
        if mask & bit(k):
            affine ^= image(k)
    row = set()
    for a in image(pivot.bit_length()-1):
        for b in affine:
            row.symmetric_difference_update({a|b})
    polynomials.append(row)
quad_rank = rank([{m for m in p if m.bit_count()==2} for p in polynomials])
full_rank = rank([p.copy() for p in polynomials])
assert quad_rank == full_rank == len(polynomials)
print(f"After marker elimination: squarefree quadratic rank = full rank = {full_rank}.")
