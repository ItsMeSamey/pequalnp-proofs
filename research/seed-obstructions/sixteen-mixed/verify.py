"""Verify both low-cost nine-point searches from the raw statement."""
from collections import Counter
from hashlib import sha256
from itertools import combinations_with_replacement
from pathlib import Path
import subprocess
import sys
import tempfile
from verify_packing import samples
base=Path(__file__).resolve().parent
source=Path(sys.argv[1]) if len(sys.argv)>1 else base/'nine.txt'
assert sha256(source.read_bytes()).hexdigest()=='b4a2755543b874f87b00321f803d63a900cef24876bcc0c445cd5020407f7479'
rows,front,target=samples(base/'L-meta-18968.json')
positive=sorted({r&((1<<20)-1) for k,r in enumerate(rows) if (target^front)>>k&1})
negative=sorted({r&((1<<20)-1) for k,r in enumerate(rows) if not target>>k&1})
maximal=[x for x in negative if not any(x!=y and not x&~y for y in negative)]
relations=sorted({(p&8191,n&8191) for p in positive for n in negative if not (p&~n)>>13})
assert (len(positive),len(maximal),len(relations))==(28,245,2961)
atoms=[1<<j for j in range(7)]
line_relations={(p>>13,n>>13) for p in positive for n in negative if not (p&~n)&8191}
def extras(paid):
    states={tuple(atoms)}
    for _ in range(paid):
        following=set()
        for state in states:
            for a,b in combinations_with_replacement(state,2):
                for val in (a&b,a|b):
                    following.add(tuple(sorted((*state,val))))
        states=following
    result=set()
    for state in states:
        for cut in set(state) if paid==2 else [None]:
            family=list(state)
            if cut is not None:family.remove(cut)
            if not all(any((m&a) and not m&b for m in family) for a,b in line_relations):continue
            assert all(m in family for m in atoms)
            for m in atoms:family.remove(m)
            assert len(family)==1
            result.add(family[0])
    return sorted(result)
line_extras={d: extras(d) for d in (1,2)}
with tempfile.TemporaryDirectory() as directory:
    work=Path(directory)
    for name in ['charge','batch16','trees']:
        subprocess.run(['c++','-O3','-std=c++20',str(base/(name+'.cpp')),'-o',str(work/name)],check=True)
    (work/'relations').write_text(''.join(f'{a} {b}\n' for a,b in relations))
    with source.open() as all_families:
        r=subprocess.run([str(work/'charge'),str(work/'relations')],stdin=all_families,capture_output=True,text=True,check=True)
    costs=[list(map(int,l.split())) for l in r.stdout.splitlines()]
    if len(sys.argv) > 2:
        Path(sys.argv[2]).write_text(r.stdout)
    hist=Counter(l[-1] for l in costs)
    assert hist=={15:15,16:108,17:918,18:2877,19:13006}
    print('Point bounds',sorted(hist.items()),flush=True)
    (work/'batchrows.txt').write_text(' '.join(map(str,[len(positive),len(maximal),*positive,*maximal])))
    low=work/'low.txt'; reps=work/'reps.txt'
    low.write_text(''.join(' '.join(map(str,row[:-1]))+'\n' for row in costs if row[-1]<=17))
    subprocess.run([sys.executable,str(base/'orbits16.py'),str(low),str(reps)],cwd=work,check=True)
    r=subprocess.run([str(work/'batch16'),str(work/'batchrows.txt'),str(reps),'2000000'],capture_output=True,text=True,check=True)
    end=Counter()
    for line in r.stdout.splitlines():
        *mask,gate,status=map(int,line.split())
        assert status==0
        end[gate]+=1
    assert end=={6:5,8:12,10:40,11:8}
    print('One-copy extinction gates',sorted(end.items()),flush=True)
    lines=[' '.join(map(str,(len(positive),len(maximal))))]
    for row in positive+maximal:lines.append(f'{row&8191} {row>>13}')
    for row in costs:
        if row[-1]<=16:
            for x in line_extras[17-row[-1]]:
                lines.append(' '.join(map(str,[*row[:-1],x])))
    r=subprocess.run([str(work/'trees')],input='\n'.join(lines)+'\n',capture_output=True,text=True,check=True)
    result=[tuple(map(int,row.split())) for row in r.stdout.splitlines()]
    assert len(result)==4092 and all(not status for _,_,status,_ in result)
    print('All',len(result),'read-once extensions rejected;',sum(x[-1] for x in result),'states.')
