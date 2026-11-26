"""Verify the missing-singleton nine-line banks by graph enumeration and point projection."""
from itertools import combinations
from pathlib import Path
import re
import subprocess
import tempfile
from inputs import N,P,stars
from samples import actions
from simplegraph import select
HERE=Path(__file__).resolve().parent
A=8191

def run():
    group=actions(P,N)
    permutations=[tuple(stars.index(f[x]) for x in stars) for f in group]
    possible=set()
    line_obligations={(a>>13,b>>13) for a in P for b in N if not (a&A)&~b}
    for t in range(7):
        for u in combinations([i for i in range(7) if i!=t],3):
            bank=[1<<i for i in range(7) if i!=t]+[(1<<t)|(1<<i) for i in u]
            if all(any(x&a and not x&b for x in bank) for a,b in line_obligations):
                possible.add((t,u))
    reps=[(0,(1,2,6)),(1,(0,2,3))]
    orbits=[{(f[t],tuple(sorted(f[i] for i in us))) for f in permutations} for t,us in reps]
    assert [len(x) for x in orbits]==[12,12] and orbits[0].isdisjoint(orbits[1])
    assert set.union(*orbits)==possible
    assert {n>>13 for n in N if all(n&s for s in stars)}=={0}
    hitting={n&A for n in N if all(n&s for s in stars)}
    assert len(hitting)==16 and all(any(q>>i&1 for q in hitting) for i in range(13))
    assert all(any(not (((1<<i)|(1<<j))&~n) for n in N) for i,j in combinations(range(13),2))
    for p in range(13):
        for j,k in combinations([j for j,T in enumerate(stars) if not(T>>p&1)],2):
            assert any(n>>p&1 and n>>(13+j)&1 and n>>(13+k)&1 for n in N)
    for j,T in enumerate(stars):
        for K,V in combinations([s for s in stars if s!=T],2):
            selected=[n&A for n in N if n>>(13+j)&1 and n&K and n&V]
            for a,b in combinations([i for i in range(13) if not T>>i&1],2):
                assert any(not (((1<<a)|(1<<b))&~q) for q in selected)
    graphs=[select(t,us) for t,us in reps]
    assert graphs[0]==graphs[1] and len(graphs[0])==118
    with tempfile.TemporaryDirectory() as td:
        work=Path(td)
        for name,src in [('private','private.cpp'),('points','point/stream11simple.cpp')]:
            subprocess.run(['c++','-O3','-march=native','-std=c++20',HERE/src,'-o',work/name],check=True)
        result=subprocess.run([work/'private'],input=''.join(f'{g}\n' for g in graphs[0]),
                              text=True,capture_output=True,check=True)
        assert not result.stdout.strip()
        counts=[]
        for line in result.stderr.splitlines():
            left,right=line.split(' good')
            invalid=int(left.split()[-1]);row=tuple(map(int,right.split()))
            assert invalid==0 and not any(row[:4]);counts.append(row)
        assert counts==[(0,0,0,0,630,94005,32805)]+[(0,0,0,0,5760,68640,0)]*3
        print(result.stderr,end='')
        raw={(a&A,b&A) for a in P for b in N if not (a>>13)&~(b>>13)}
        maximal=sorted((a,b) for a,b in raw if not any(a==c and b!=d and not b&~d for c,d in raw))
        assert len(maximal)==1323
        point_input=' '.join(map(str,stars))+'\n'+'0 0\n'*7+''.join(f'{a} {b}\n' for a,b in maximal)
        raw55={1<<i for i in range(13)}
        raw31=set(raw55)
        for i in range(6):
            x=(1<<i)|(1<<(i+1));y=(1<<((i+3)%13))|(1<<((i+9)%13));raw31.update((x,y,x|y))
        raw55=sorted({f[x] for f in group for x in raw31})
        assert len(raw55)==55
        literal=re.search(r'orbitraw\[\]\s*=\s*\{([^}]+)\}',(HERE/'point/hereditaryrole.hpp').read_text(),re.DOTALL)
        assert literal and [int(x) for x in literal[1].split(',')]==raw55
        quartet_reps=sorted({min(sum(1<<f[i] for i in g) for f in permutations) for g in combinations(range(7),4)})
        assert quartet_reps==[15,23,27,46,83]
        for rep,expected in zip(quartet_reps,[4309,1902,1498,4002,5014]):
            cert=HERE/f'pairanchors-{rep}.txt'
            anchors=[tuple(map(int,l.split())) for l in cert.read_text().splitlines()]
            active={s for i,s in enumerate(stars) if rep>>i&1}
            assert len(anchors)==7 and {p for p,n in anchors[:4]}==active
            assert all(not p&n and n.bit_count()==2 for p,n in anchors[:4]) and all(x in maximal for x in anchors[4:])
            assert all(a&d or c&b for (a,b),(c,d) in combinations(anchors,2))
            result=subprocess.run([work/'points',str(rep),cert],input=point_input,text=True,capture_output=True,check=True)
            assert not result.stdout.strip() and f'DONE {expected} 0 0' in result.stderr
            print('point quartet',rep,expected,'nodes, zero banks')
    print('All 24 missing-singleton line banks excluded.')
if __name__=='__main__':
    if not __debug__: raise SystemExit('Enable Python assertions.')
    run()
