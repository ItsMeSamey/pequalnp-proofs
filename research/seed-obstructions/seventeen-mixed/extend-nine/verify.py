"""Replay the P10 superset filter. Argument 1 is the archived sixteen directory."""
import shutil
import hashlib
import itertools
from pathlib import Path
import subprocess
import sys
import tempfile

here = Path(__file__).resolve().parent
source = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(source))
from verify_packing import samples

bases = source / 'nine.txt'
assert hashlib.sha256(bases.read_bytes()).hexdigest() == 'b4a2755543b874f87b00321f803d63a900cef24876bcc0c445cd5020407f7479'
rows, front, target = samples(source / 'L-meta-18968.json')
positive = {row & ((1<<20)-1) for i,row in enumerate(rows) if (front^target)>>i&1}
negative = {row & ((1<<20)-1) for i,row in enumerate(rows) if not target>>i&1}
maximal = {s for s in negative if not any(s!=t and not s&~t for t in negative)}
relations = sorted({(p&8191,n&8191) for p in positive for n in negative if not (p&~n)>>13})
assert len(relations)==2961
lines = [sum(1<<((j+6+d)%13) for d in (0,1,3,9)) for j in range(7)]
stars = [sum(((t>>p)&1)<<j for j,t in enumerate(lines)) for p in range(13)]
def image(mask, perm):
    return sum(1<<dest for index,dest in enumerate(perm) if mask>>index&1)
group = []
for order in itertools.permutations(range(7)):
    moved = [image(star,order) for star in stars]
    if set(moved)!=set(stars):continue
    points = [stars.index(t) for t in moved]
    def transform(row):
        return image(row&8191,points) | image(row>>13,order)<<13
    if {transform(r) for r in positive}!=positive:continue
    if {transform(r) for r in maximal}!=maximal:continue
    group.append(points)
assert len(group)==24
primitives={1<<p for p in range(13)}
for j in range(6):
    a,b,c,d=[1<<((j+k)%13) for k in (0,1,3,9)]
    primitives.update([a|b,c|d,a|b|c|d])
unions={0}
for _ in range(4):
    unions={u|v for u in unions for v in primitives}
assert max(sum(not t&~u for t in lines) for u in unions)==2

hashes = ['56e1556beff48efb2bad172d081ba10e63c6991305f231050809a6b989d042e7',
          '965c57b4da2c3ce69da0992f5d1c1a6e2eb30ab8e93b8a8e30f1af4a6e0622fe']
with tempfile.TemporaryDirectory() as folder:
    work=Path(folder)
    (work/'relations').write_text(''.join(f'{p} {n}\n' for p,n in relations))
    (work/'group').write_text(''.join(' '.join(map(str,p))+'\n' for p in group))
    for prog in ['augment','orbits']:
        subprocess.run(['c++','-std=c++20','-O3',str(here/(prog+'.cpp')),'-o',str(work/prog)],check=True)
    for mode,digest in enumerate(hashes):
        families=work/'families'
        subprocess.run([work/'augment',work/'relations',bases,families,str(mode)],check=True)
        with families.open() as f:
            reps=subprocess.run([work/'orbits',work/'group','16'],stdin=f,capture_output=True,check=True)
        print(reps.stderr.decode().strip(),flush=True)
        assert hashlib.sha256(reps.stdout).hexdigest()==digest
        if len(sys.argv)>2:
            dest=Path(sys.argv[2])/('duplicate-reps.txt' if mode else 'distinct-reps.txt')
            dest.write_bytes(reps.stdout)
            shutil.copyfile(families,Path(sys.argv[2])/("duplicate-survivors.txt" if mode else "distinct-survivors.txt"))
