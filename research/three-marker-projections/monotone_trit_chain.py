"""Physical successor table and complete small-chain verification."""
from itertools import product

def compile_chain(n):
    if n < 1:
        raise ValueError("empty chain")
    base = (4, 5, 3, 6, 2, 1, 0)
    auxiliary = (4, 0, 3)
    w = {}
    for j in range(n):
        for i, dest in enumerate(base):
            w[j,i] = (j,7+auxiliary.index(dest) if dest in auxiliary else dest)
        for i, dest in enumerate(auxiliary):
            w[j,7+i] = (j,dest)
    for j in range(n-1):
        tail = next(k for k,v in w.items() if v==(j+1,0))
        w[j,2],w[tail] = w[tail],w[j,2]
    ins, outs = {}, {}
    def gate(inputs,outputs):
        g=len(ins)//3
        for i,(a,b) in enumerate(zip(inputs,outputs)):
            ins[a]=3*g+i
            outs[b]=3*g+i
    for ports in ((4,5,6),(7,8,9)):
        for j in range(n):
            raw=[(j,p) for p in ports]
            gate(raw,raw)
    for j in range(n+1):
        if j in (0,n):
            raw=[(0,0),(0,1),('dummy',j)] if j==0 else [(n-1,2),(n-1,3),('dummy',j)]
            w[raw[2]]=raw[2]
            gate(raw,raw)
        else:
            gate([(j-1,2),(j-1,3),(j,1)],[(j,0),(j-1,3),(j,1)])
    wiring={outs[a]:ins[b] for a,b in w.items() if a in outs}
    assert sorted(wiring)==sorted(wiring.values())==list(range(3*(3*n+1)))
    return wiring,ins[0,0],ins[w[n-1,2]]

def joined(circuit,settings):
    wiring,start,target=circuit
    site=start
    while True:
        if site==target:
            return True
        g,i=divmod(site,3)
        site=wiring[3*g+(i+settings[g])%3]
        if site==start:
            return False

if __name__=='__main__':
    for n in (1,2,3):
        circuit=compile_chain(n)
        count=0
        for t in product(range(3),repeat=n):
            for a in product(range(2),repeat=n):
                for s in product(range(2),repeat=n+1):
                    want=all(( (515,672)[a[j]] >> (4*t[j]+2*s[j+1]+s[j]) ) & 1 for j in range(n))
                    assert joined(circuit,t+a+s)==want,(n,t,a,s)
                    count+=1
        print(n,count)
