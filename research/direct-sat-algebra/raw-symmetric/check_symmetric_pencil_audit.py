"""Independent bit-level parity and hostiles for normalized symmetric pencils."""
from itertools import product
from random import Random
from punctured_witness import BinaryField


def nonsingular(rows):
    pivots={}
    for x in rows:
        while x:
            j=x.bit_length()-1
            if j not in pivots:
                pivots[j]=x
                break
            x ^= pivots[j]
        else:
            return False
    return True


def check():
    rng=Random(566)
    tested=0
    for n in (1,2,3,4,6):
        for _ in range(32):
            # Arbitrary off-diagonal affine Boolean forms, arbitrary fixed
            # nonsymmetric binary drift; diagonal coordinates are independent.
            entries={(i,j):rng.randrange(1<<(n+1)) for i in range(n) for j in range(i)}
            drift=[rng.randrange(1<<n) for _ in range(n)]
            good=0
            for t in range(1<<n):
                rows=[a^((t>>i&1)<<i) for i,a in enumerate(drift)]
                for (i,j),v in entries.items():
                    b=(v & (t | (1<<n))).bit_count()%2
                    rows[i] ^= b<<j
                    rows[j] ^= b<<i
                good+=nonsingular(rows)
            assert good%2
            tested+=1
    f=BinaryField(7)
    # For off-diagonal s² the K-Schur scalar becomes t*s+s^4=(t+1)*s.
    good=[(t,s) for t,s in product(range(4),repeat=2)
          if f.mul(t,s)^f.mul(f.mul(s,s),f.mul(s,s))]
    assert sum(t==1 for t,s in good)==0 and len(good)==9
    # GF2 normalized 2x2 case: greedy first nonsingular leading minor is fatal.
    assert [(t,s) for t,s in product(range(2),repeat=2) if t*s^s*s]==[(0,1)]
    print(tested,"symmetric bit pencils with nonsymmetric drift, plus GF2 and GF4 greedy failures verified")


if __name__=="__main__":
    check()
