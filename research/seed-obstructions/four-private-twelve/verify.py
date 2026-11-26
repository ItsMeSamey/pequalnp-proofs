"""Verify the four-group point lower bound at width twelve."""
from itertools import combinations
from pathlib import Path
import re
import subprocess
import tempfile
import sys
HERE=Path(__file__).resolve().parent
BASE=Path(sys.argv[1]) if len(sys.argv)==2 else HERE.parent / 'four-private-groups'
sys.path.insert(0,str(BASE))
from inputs import N,P,stars
from samples import actions
HERE=Path(__file__).resolve().parent
A=8191

def run():
    group=actions(P,N)
    permutations=[tuple(stars.index(f[x]) for x in stars) for f in group]
    with tempfile.TemporaryDirectory() as td:
        work=Path(td)
        subprocess.run(['c++','-O3','-march=native','-std=c++20',HERE/'point/search.cpp','-o',work/'points'],check=True)
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
        for rep,expected in zip(quartet_reps,[228607,86153,90893,208315,923641]):
            cert=BASE/f'pairanchors-{rep}.txt'
            anchors=[tuple(map(int,l.split())) for l in cert.read_text().splitlines()]
            active={s for i,s in enumerate(stars) if rep>>i&1}
            assert len(anchors)==7 and {p for p,n in anchors[:4]}==active
            assert all(not p&n and n.bit_count()==2 for p,n in anchors[:4]) and all(x in maximal for x in anchors[4:])
            assert all(a&d or c&b for (a,b),(c,d) in combinations(anchors,2))
            result=subprocess.run([work/'points',str(rep),cert],input=point_input,text=True,capture_output=True,check=True)
            assert not result.stdout.strip() and f'DONE {expected} 0 0' in result.stderr
            print('point quartet',rep,expected,'nodes, zero banks')
    print('All twelve-slot banks with four disjoint pair-safe guard groups require at least 12 point gates.')
if __name__=='__main__':
    if not __debug__: raise SystemExit('Enable Python assertions.')
    run()
