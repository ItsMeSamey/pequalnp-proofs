"""Replay the 17-mixed P10/L7 cases from the three point-family lists."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

def raw_samples(path):
    statement = json.loads(path.read_text())['formal_statement']
    assert sha256(statement.encode()).hexdigest() == 'd5fbefe3ea85033034056aae8ed0b90ecfe428b8a69e3456176309d0c82b54c2'
    blocks = re.findall(r'\[((?:\(\d+ : ℕ\)(?:, )?)+)\]', statement)
    assert len(blocks) == 2
    columns = []
    for block in blocks:
        seed = 0
        for part in re.findall(r'\((\d+) : ℕ\)', block):
            seed = seed * 10**19 + int(part)
        for shift in range(13):
            col = 0
            for start in range(0, 676, 13):
                lane = (seed >> start) & 8191
                col |= (((lane << shift) | (lane >> (13-shift))) & 8191) << start
            columns.append(col)
    front, target = [int(re.search(r'x1 \(' + str(j) + r' : ℕ\) = \((\d+) : ℕ\)', statement)[1])
                     for j in (54, 88)]
    relevant = columns[:13] + columns[19:26]
    rows = [sum(((col >> i) & 1) << j for j,col in enumerate(relevant)) for i in range(676)]
    pos = {r for i,r in enumerate(rows) if (target ^ front) >> i & 1}
    neg = {r for i,r in enumerate(rows) if not target >> i & 1}
    neg = {r for r in neg if all(r == s or r & ~s for s in neg)}
    assert len(pos) == 28 and len(neg) == 245
    return pos, neg

def permute(mask, images):
    return sum(1 << v for j,v in enumerate(images) if mask >> j & 1)

def actions(pos, neg):
    stars = [sum(1 << ((6+j+d) % 13) for d in (0,1,3,9)) for j in range(7)]
    incidence = [sum(bool(s >> p & 1) << j for j,s in enumerate(stars)) for p in range(13)]
    assert len(set(incidence)) == 13
    group = []
    for lines in permutations(range(7)):
        moved = [permute(i,lines) for i in incidence]
        if set(moved) != set(incidence):
            continue
        points = [incidence.index(i) for i in moved]
        pm = [0]*8192
        for v in range(1,8192):
            bit = v & -v
            pm[v] = pm[v^bit] | (1 << points[bit.bit_length()-1])
        lm = [permute(v,lines) << 13 for v in range(128)]
        def move(r):
            return pm[r & 8191] | lm[r >> 13]
        if {move(r) for r in pos} == pos and {move(r) for r in neg} == neg:
            group.append(pm)
    assert len(group) == 24
    return group

def records(path, width):
    result = [tuple(map(int,line.split())) for line in path.read_text().splitlines() if line.strip()]
    assert all(len(row) == width for row in result)
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('statement','refined','nine','distinct','duplicate'):
        parser.add_argument(name,type=Path)
    parser.add_argument('--cxx',default='c++')
    parser.add_argument('--certified-reps',action='store_true',help='consume the two hash-pinned outputs of the augmentation verifier')
    args = parser.parse_args()
    pos, neg = raw_samples(args.statement)
    group = actions(pos,neg)
    nine = records(args.nine,9)
    assert len(nine) == 16924
    def augmented(path, duplicate):
        family = set()
        source = records(path,3)
        for index, mask, lower in source:
            assert 1 <= index <= len(nine) and 0 <= mask < 8192
            base = nine[index-1]
            assert duplicate == (mask == 0 or mask in base)
            if lower <= 16:
                family.add(tuple(sorted((*base,mask))))
        return family
    refined = {tuple(sorted(row[:10])) for row in records(args.refined,11) if row[10] <= 16}
    collections = [('irreducible',refined,23274,1123)]
    if args.certified_reps:
        for label,path,digest,expected in [
            ('distinct extension',args.distinct,'56e1556beff48efb2bad172d081ba10e63c6991305f231050809a6b989d042e7',1713),
            ('repeat or zero',args.duplicate,'965c57b4da2c3ce69da0992f5d1c1a6e2eb30ab8e93b8a8e30f1af4a6e0622fe',65)]:
            assert sha256(path.read_bytes()).hexdigest() == digest
            families = set(records(path,10))
            assert all(min(tuple(sorted(pm[m] for m in f)) for pm in group)==f for f in families)
            collections.append((label,families,expected,expected))
    else:
        collections += [
            ('distinct extension',augmented(args.distinct,False),26664,1713),
            ('repeat or zero',augmented(args.duplicate,True),1122,65)]
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp)/'one-copy'
        subprocess.run([args.cxx,'-std=c++17','-O3',str(HERE/'frontier.cpp'),'-o',str(exe)],check=True)
        for label, families, count, num_reps in collections:
            assert len(families) == count
            assert all(len(f) == 10 and all(0 <= m < 8192 for m in f) for f in families)
            reps = sorted({min(tuple(sorted(pm[m] for m in f)) for pm in group) for f in families})
            assert len(reps) == num_reps
            data = [len(pos),len(neg),*sorted(pos),*sorted(neg),len(reps)]
            data = ' '.join(map(str,data))+'\n'+''.join(' '.join(map(str,r))+'\n' for r in reps)
            result = subprocess.run([str(exe)],input=data,text=True,capture_output=True,check=True)
            depths = [int(d) for d in result.stdout.splitlines()]
            assert len(depths) == len(reps) and all(1 <= d <= 17 for d in depths)
            print(label, len(families), 'distinct families,', len(reps), 'representatives, extinction depths', sorted(Counter(depths).items()),flush=True)

if __name__ == '__main__':
    main()
