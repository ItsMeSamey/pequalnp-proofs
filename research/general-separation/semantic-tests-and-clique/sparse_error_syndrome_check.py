"""Read syndromes only from the corrupted table, including all coordinate slices."""
from collections import Counter
from random import Random

def gf_mul(x,y):
    z=0
    while y:
        if y&1:z^=x
        y>>=1
        x<<=1
        if x&32:x^=0b100101 # x^5+x^2+1
    return z

def table(q,t):
    powers=[1]
    for _ in range(q-1):powers.append(gf_mul(powers[-1],t))
    h=[0]
    for v in powers:h += [y^v for y in h]
    return h

def candidates(h,ones):
    odd=[0]*32
    labels=[0]*32
    for x in ones:
        b=h[x]
        odd[b]^=1
        labels[b]^=x # bit i is the parity of coordinate-i=1 in this bucket
    return frozenset(labels[b] for b in range(32) if odd[b])

rng=Random(472)
q=10
hashes=[table(q,t) for t in range(32)]
assert len({gf_mul(a,9) for a in range(32)})==32
cases=0
for d in range(4): # d+u+1<q
    monos=[m for m in range(1<<q) if m.bit_count()<=d]
    for _ in range(4):
        chosen=[m for m in monos if rng.randrange(3)==0]
        clean={x for x in range(1<<q) if sum(x&m==m for m in chosen)%2}
        # Stronger check: all (including even buckets') raw bit-slice parities vanish.
        for h in hashes:
            totals=[0]*32
            for x in clean:totals[h[x]]^=(1<<q)|x
            assert not any(totals)
        for e in range(3):
            errors=set(rng.sample(range(1<<q),e))
            outputs=[candidates(h,clean^errors) for h in hashes]
            counts=Counter(outputs)
            assert counts[frozenset(errors)]>len(hashes)//2
            votes=Counter(x for row in outputs for x in row)
            assert {x for x,c in votes.items() if 2*c>len(hashes)}==errors
            assert all(row==candidates(h,errors) for h,row in zip(hashes,outputs))
            cases+=1

bad={2,4,8}
assert candidates(hashes[0],bad)=={14} and 14 not in bad
# Single error can be completely hidden by a forbidden degree-q point indicator.
hidden={(1<<q)-1}
assert not any(candidates(h,hidden^hidden) for h in hashes)
# At the exact degree boundary an odd-bucket decoder can fail purely via a
# nonzero coordinate slice, even though every clean bucket parity vanishes.
d=q-5-1
t=2 # 1,t,t^2,t^3,t^4 independent
mon=(1<<q)-(1<<(q-d)) # fixes the last four coordinates to one
clean={x for x in range(1<<q) if x&mon==mon}
h=hashes[t]
sy=[0]*32
for x in clean:sy[h[x]]^=(1<<q)|x
assert all(v and v<1<<q for v in sy)
assert candidates(h,clean^{0})!={0}
print(cases,'majority recoveries, exact cancellation, triple collision and two violated-degree controls passed')
