"""Recover signed private transpositions acting as frontier flips."""
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-coset-native'))
from coset import insert,kernel,equations_for_group,lift,parity,translate

def signed_swaps(n,tables,front):
    seen={v for s in tables for v in s}
    private=sorted(v for v in seen if not front>>(v-1)&1)
    eq={s:equations_for_group(s,t) for s,t in tables.items()}
    for d in kernel(n,[r for rr in eq.values() for r in rr]):
        if d&front:
            yield d&front,(0,0,d)
    for x,y in combinations(private,2):
        rows={}
        for s,t in tables.items():
            mapped=[y if v==x else x if v==y else v for v in s]
            dest=tuple(sorted(mapped))
            if dest not in tables: break
            pt=0
            for i in range(1<<len(s)):
                if t>>i&1:
                    j=sum((i>>k&1)<<dest.index(v) for k,v in enumerate(mapped))
                    pt|=1<<j
            delta=next((i for i in range(1<<len(s)) if translate(pt,i)==tables[dest]),None)
            if delta is None: break
            shift=lift(delta,dest)
            ok=True
            for row in eq[dest]:
                rest,rhs=insert(rows,row,parity(row&shift))
                if not rest and rhs:
                    ok=False
                    break
            if not ok: break
        else:
            word=0
            for p in sorted(rows):
                row,rhs=rows[p]
                if parity(word&row)!=rhs: word^=1<<p
            if word&front:
                yield word&front,(x,y,word)
