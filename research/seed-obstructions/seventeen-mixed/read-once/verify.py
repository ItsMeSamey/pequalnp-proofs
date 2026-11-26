"""Replay the 17-mixed, ten-point/eight-line certificate using the local inputs."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from verify_packing import samples

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def coordinates(row):
    return row & 8191, (row >> 13) & 127


def main():
    for record in (HERE / 'SHA256SUMS').read_text().splitlines():
        digest, name = record.split()
        require(sha256((HERE / name).read_bytes()).hexdigest() == digest, name)
    rows, front, target = samples(HERE / 'L-meta-18968.json')
    p = sorted({coordinates(row) for i,row in enumerate(rows) if (target ^ front) >> i & 1})
    n = {coordinates(row) for i,row in enumerate(rows) if not (target >> i & 1)}
    maximal = sorted((a,b) for a,b in n if not any((a,b) != (c,d) and
                     not (a & ~c or b & ~d) for c,d in n))
    require((len(p),len(maximal)) == (28,245), 'sample counts')
    header = [f'{len(p)} {len(maximal)}'] + [f'{a} {b}' for a,b in p+maximal]
    stars = [sum(1 << ((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
    control = [(0, stars+stars[:3])]
    # e=0 can be absorbed as an OR with any mixed wire. Three repeated
    # point leaves can be absorbed by AND into their matched mixed stars.
    with TemporaryDirectory() as tmp:
        executable = Path(tmp) / 'tree'
        subprocess.run(['c++','-std=c++20','-O2',str(HERE/'tree.cpp'),'-o',str(executable)],check=True)
        for name, count, expected in [
            ('positive control', 1, (1,1,1)),
            ('refined-all.txt', 6543, (252005,0,0)),
            ('geom_reps.txt', 1713, (219264,0,0)),
            ('dupgeom_reps.txt', 65, (8320,21,0)),
        ]:
            cases = []
            if name == 'positive control':
                cases = control
            else:
                for record in (HERE/name).read_text().splitlines():
                    family = list(map(int,record.split()))
                    if name == 'refined-all.txt':
                        lower = family.pop()
                        if lower > 15:
                            continue
                        cap = min(7,17-lower)
                    else:
                        cap = 7
                    require(len(family)==10, 'malformed family')
                    cases.append((cap,family))
            require(len(cases)==count,name)
            feed = '\n'.join(header+[' '.join(map(str,[cap]+family)) for cap,family in cases])+'\n'
            result = subprocess.run([executable],input=feed,text=True,capture_output=True,check=True)
            tested = sum(sum(e.bit_count() <= cap for e in range(128)) for cap,_ in cases)
            reports = [tuple(map(int,line.split())) for line in result.stdout.splitlines()]
            require(len(reports)==count and all(len(r)==2 for r in reports),'result count')
            totals = tested,sum(r[0] for r in reports),sum(r[1] for r in reports)
            require(totals == expected, (name,totals,expected))
            print(name, 'families', count, 'tests', tested, 'after guard', totals[1],
                  'separating trees', totals[2], flush=True)


if __name__ == '__main__':
    main()
