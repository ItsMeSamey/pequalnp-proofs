#!/usr/bin/env python3
"""Rebuild the five-region obstruction and independently check its RUP proof."""
import argparse
import hashlib
import itertools
import json
from collections import defaultdict
from pathlib import Path

CARE_SHA256 = '16199778bdce2ba5ae48b6c55ec730f73f7059c0e58857ec7fa837f9b58f8879'
CNF_SHA256 = 'a839cb8c6206553359dfa5014a295cd5222b7af2f1e0c8b84d5eb4b23ae7ad08'


def encode(path):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != CARE_SHA256:
        raise ValueError('projected care source digest mismatch')
    care = dict(json.loads(raw)['care'])
    desc = [(x,y) for x in care if care[x] for y in care if not care[y] and x & y == x]
    lows, highs = {x for x,y in desc}, {y for x,y in desc}
    supported = {h & ~l for h in highs for l in lows if (h & ~l).bit_count() == 1}
    if supported != {1 << i for i in range(21)}:
        raise ValueError('missing essential feature')
    highs = sorted(h for h in highs if not any(z != h and z & h == z for z in highs))
    lows = sorted(l for l in lows if not any(z != l and z & l == l for z in lows))
    names = {}
    clauses = []
    def var(*key):
        return names.setdefault(key,len(names)+1)
    for i in range(21):
        clauses.append([var('color',i,t) for t in range(5)])
    for i,j in itertools.combinations(range(21),2):
        for t in range(5):
            clauses.append([-var('color',i,t),-var('color',j,t),var('same',i,j)])
    for h in highs:
        for l in lows:
            diff = [i for i in range(21) if (h & ~l) >> i & 1]
            clauses.append([var('pos',h,i) for i in diff])
            clauses.append([var('neg',l,i) for i in diff])
            for t in range(4):
                clauses.append([-var('true',h,t),-var('false',l,t)]
                               + [var('color',i,k) for i in diff for k in range(t+1)])
            for i,j in itertools.combinations(diff,2):
                clauses.append([-var('pos',h,i),-var('pos',h,j),-var('neg',l,i),
                                -var('neg',l,j),-var('same',i,j)])
    for i in range(21):
        for j,k in itertools.combinations(range(5),2):
            clauses.append([-var('color',i,j),-var('color',i,k)])
        for t in range(4):
            for h in highs:
                if h >> i & 1:
                    clauses.append([-var('pos',h,i),-var('color',i,t),var('true',h,t)])
            for l in lows:
                if not l >> i & 1:
                    clauses.append([-var('neg',l,i),-var('color',i,t),var('false',l,t)])
    header = f'p cnf {len(names)} {len(clauses)}\n'
    dimacs = header + ''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
    if hashlib.sha256(dimacs.encode('ascii')).hexdigest() != CNF_SHA256:
        raise ValueError('rebuilt five-region formula digest mismatch')
    return len(names),clauses,dimacs


class RupChecker:
    """Monotone database: ignoring deletion hints retains only implied lemmas."""
    def __init__(self, nvars, clauses):
        self.nvars = nvars
        self.watches = defaultdict(list)
        self.units = []
        self.inconsistent = False
        for c in clauses:
            self.add(c)

    def add(self,c):
        clause = list(dict.fromkeys(c))
        if any(-lit in clause for lit in clause):
            return
        if not clause:
            self.inconsistent = True
        elif len(clause)==1:
            self.units.append(clause[0])
        else:
            self.watches[clause[0]].append(clause)
            self.watches[clause[1]].append(clause)

    def conflicts(self,clause):
        if self.inconsistent:
            return True
        # -1, 0, 1 denote false, unassigned, true for the positive variable.
        values = [0]*(self.nvars+1)
        queue = self.units+[-lit for lit in clause]
        for literal in queue:  # Python lists include newly appended implications.
            i = abs(literal)
            sign = 1 if literal>0 else -1
            if values[i]==sign:
                continue
            if values[i]==-sign:
                return True
            values[i]=sign
            watched = self.watches[-literal]
            k=0
            while k<len(watched):
                c=watched[k]
                if c[0]==-literal:
                    c[0],c[1]=c[1],c[0]
                other=c[0]
                other_sign=1 if other>0 else -1
                if values[abs(other)]==other_sign:
                    k+=1
                    continue
                for j in range(2,len(c)):
                    alternate=c[j]
                    if values[abs(alternate)] != (-1 if alternate>0 else 1):
                        c[1],c[j]=alternate,c[1]
                        watched[k]=watched[-1]
                        watched.pop()
                        self.watches[alternate].append(c)
                        break
                else:
                    if values[abs(other)]==-other_sign:
                        return True
                    queue.append(other)
                    k+=1
        return False

    def verify(self,proof):
        additions=0
        ended=False
        with proof.open(encoding='ascii') as f:
            for line_no,line in enumerate(f,1):
                parts=line.split()
                if not parts or parts[0]=='c':
                    continue
                if ended:
                    raise ValueError(f'proof continues after empty clause at line {line_no}')
                deletion=parts[0]=='d'
                if deletion:
                    parts=parts[1:]
                if not parts or parts[-1]!='0':
                    raise ValueError(f'unterminated clause at line {line_no}')
                c=[int(x) for x in parts[:-1]]
                if any(not 0<abs(lit)<=self.nvars for lit in c):
                    raise ValueError(f'invalid literal at line {line_no}')
                if deletion:
                    continue
                if not self.conflicts(c):
                    raise ValueError(f'clause fails reverse unit propagation at line {line_no}')
                self.add(c)
                additions+=1
                ended=not c
        if not ended:
            raise ValueError('proof does not finish with a verified empty clause')
        return additions


def main():
    p=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    p.add_argument('--care',type=Path,default=here/'paid26-alias-ac6.json')
    p.add_argument('--proof',type=Path,default=here/'precone-region-5.drup')
    p.add_argument('--write-cnf',type=Path)
    a=p.parse_args()
    n,clauses,dimacs=encode(a.care)
    if a.write_cnf:
        a.write_cnf.write_bytes(dimacs.encode('ascii'))
    additions=RupChecker(n,clauses).verify(a.proof)
    print(f'Verified {len(clauses)} clauses and {additions} RUP additions. '
          'Five regions are infeasible. The sole-NOT operand requires at least 25 gates.')


if __name__=='__main__':
    try:
        main()
    except (OSError,ValueError) as e:
        raise SystemExit(str(e))
