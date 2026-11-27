"""Exact arithmetic in protected-dense-signature-401.md."""
from fractions import Fraction
q = 401
raws = 2 * (q*q + q + 1)
theta = 2 * (q + 2)
rounds, batch = 1617, 24
slack = rounds - 1
deletions = rounds * batch
threshold = batch + 2
h = q + 1 - threshold
assert h*h > deletions
max_marks = deletions*(h-1) // (h*h-deletions)
sole = 6461 + 3382 + 2*slack
protected = theta + 4*max_marks + 2*slack
excess = sole + slack - 3
group_lower = Fraction(raws-deletions-sole-protected, 2)
group_upper = 1+sole+3*excess+Fraction(4*raws, batch+1)+4*protected
assert (max_marks, sole, protected, excess) == (141,13075,4602,14688)
assert (group_lower, group_upper) == (Fraction(265921,2), Fraction(3178324,25))
assert group_lower > group_upper
print(2*raws - 4 + rounds, group_lower, group_upper)
