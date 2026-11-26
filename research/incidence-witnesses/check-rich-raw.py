"""Check the two-trigger inclusion probabilities and exact q401 thresholds."""
from fractions import Fraction
from itertools import product

for t in (1, 2):
    for bits in product((0, 1), repeat=t+1):
        *lines, raw = bits
        extra = int(any(lines) and not raw)
        bound = sum(lines) - raw * sum(lines)
        if t == 2:
            bound -= lines[0] * lines[1]
        assert extra >= bound

q, h = 401, 33
N = q*q+q+1
D = h*(q+1)+1
E = 1+2*h*(q+1)+h*h*q
p = Fraction(D,N)
Js = Fraction(D*(D-1), N*(N-1))
J = max(Js, Fraction(E,N*(q+1)), Fraction(D*D-E,N*(N-q-1)))
baseline = (p-J/2)*4*N
unit = p-J-Js/2
assert baseline+76883*unit < 56281 <= baseline+76884*unit
assert baseline+384*200*unit < 56281 <= baseline+385*200*unit
print("All extra-event inequalities and both exact thresholds passed.")
