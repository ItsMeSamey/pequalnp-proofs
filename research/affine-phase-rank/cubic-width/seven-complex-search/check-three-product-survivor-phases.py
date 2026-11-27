"""Check the relative phase needed to combine every compatible survivor pair."""
import runpy
from pathlib import Path
from fractions import Fraction
from itertools import combinations, product
import numpy as np

base = runpy.run_path(str(Path(__file__).with_name("check-three-product-survivors.py")))
I, g, rays = (base[key] for key in ("identity", "g", "rays"))
z = np.arange(8)
all_paulis = [np.array([(-1)**((x & t).bit_count()) for x in range(8)])[:, None] *
              I[z ^ s] for s, t in product(range(8), repeat=2)]

for a,k in ((g*(z<4),1),(-2*(z==7),1),(g+2*(z==7),Fraction(1,2))):
    p = g-a
    found=0
    codes=[]
    for s,t in combinations(base["signed_checks"](a),2):
        Q=(I+s)@(I+t)
        if np.trace(Q)!=8 or any(np.array_equal(Q,h) for h in codes):
            continue
        codes.append(Q)
        aperp=next(r for op in all_paulis if
                   np.vdot(a,r:=op@a)==0 and np.array_equal(Q@r,4*r))
        P=4*I-Q
        target=P@p
        pos=next(i for i in range(8) if target[i])
        for e in rays:
            actual=P@e
            if not actual[pos] or not np.array_equal(actual*target[pos],target*actual[pos]):
                continue
            unum=target[pos]*e-actual[pos]*p
            numer=np.vdot(aperp,unum)
            if not numer: continue
            denom=actual[pos]*np.vdot(a,a)
            assert any(numer*k.denominator==denom*k.numerator*r for r in (1,-1,1j,-1j))
            found+=1
    print("phase-compatible local choices", found)
