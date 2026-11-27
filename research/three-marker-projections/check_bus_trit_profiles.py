from itertools import product
from pathlib import Path

def boundary(bits):
    n=len(bits)
    p=list(range(n+2))
    for i,bit in enumerate(bits):
        k=i+bit
        p[k],p[k+1]=p[k+1],p[k]
    pins=[0,1,n,n+1]
    ret=[]
    for pin in pins:
        v=p[pin]
        while v not in pins:
            v=p[v]
        ret.append(pins.index(v))
    return tuple(ret)

def trace(p,bus,t):
    steps=list(bus)+[4+(k+t)%3 for k in range(3)]+[7,8]
    v=7
    while True:
        v=p[steps[v]]
        if v==8:return True
        if v==7:return False

def code(p,buses):
    return sum(1<<(3*j+t) for j,b in enumerate(buses) for t in range(3) if trace(p,b,t))

def main():
    buses=[(1,2,0,3),(0,2,3,1),(0,1,2,3),(1,0,2,3),(0,1,3,2),(1,0,3,2)]
    for n in range(2,11):
        for bits in product((0,1),repeat=n):
            idx=buses.index(boundary(bits))
            assert idx==(bits[0]) if len(set(bits))==1 else idx>=2
    rows=Path(__file__).with_name('bus_trit_profiles.txt').read_text().splitlines()
    codes=set()
    for row in rows:
        target,*p=map(int,row.split())
        assert sorted(p)==list(range(9)) and code(p,buses)==target<64
        codes.add(target)
    missing={1<<a|1<<(3+b) for a in range(3) for b in range(3) if a!=b}
    assert codes==set(range(64))-missing-{63^x for x in missing}
    p=(0,4,7,2,5,1,8,3,6)
    rot=(5,1,2,3,4,6,0,7,8)
    q=tuple(rot[i] for i in p)
    assert (code(p,buses)|code(q,buses))==46
    print('52 raw profiles, 6 more using a single auxiliary, 2044 explicit bus words')
if __name__=='__main__':main()
