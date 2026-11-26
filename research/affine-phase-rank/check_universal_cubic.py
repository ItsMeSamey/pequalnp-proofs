from itertools import product
from random import Random
rng=Random(90703)
num=0
for s in range(1,6):
    for trial in range(15):
        n=3
        gates=[(rng.randrange(n+i),rng.randrange(n+i),rng.randrange(16)) for i in range(s)]
        for x in range(1<<n):
            inputs=[x>>i&1 for i in range(n)]
            wires=inputs.copy()
            for a,b,t in gates:
                wires.append(t>>(wires[a]+2*wires[b])&1)
            total=0
            for y in range(1<<s):
                w=inputs+[y>>i&1 for i in range(s)]
                violations=sum(((w[n+i]^(t>>(w[a]+2*w[b])&1))<<i) for i,(a,b,t) in enumerate(gates))
                total+=sum((-1)**((z&violations).bit_count()+w[-1]) for z in range(1<<s))
            assert total==(1<<s)*(-1)**wires[-1]
            num+=1
det=0
for a,b,c in product(range(8), repeat=3):
    derivative=sum(int((i&7)==7) for i in (0,a,b,c,a^b,a^c,b^c,a^b^c))%2
    det+=derivative
assert det==168
print(f"{num} path-sum inputs; {det} nonzero cubic derivatives among 512 directions")
