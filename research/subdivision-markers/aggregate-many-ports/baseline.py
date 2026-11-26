"""Construct witness charts for line ports and certified larger ports."""
from itertools import combinations
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/'unseeded-root-states'))
from solve import canonical, image, solve, eliminate

def basis_indices(cols):
    piv,_=eliminate(cols)
    return sorted(support.bit_length()-1 for _,support in piv.values())

def family(cols,tags,port):
    cols=tuple(cols)
    U=tuple(port)
    B=basis_indices(cols)
    basis=tuple(cols[e] for e in B)
    P=tuple(solve(basis,p) for p in U)
    if any(v is None for v in P):
        if len(U)>1:
            return None
        _,single=family(cols,tags,())
        return 'absent',single
    J=tuple(e for e in range(len(cols)) if e not in B)
    chord={e:solve(basis,cols[e]) for e in J}
    size=len(U)
    for E in combinations(range(len(B)),size):
        rho=tuple(sum(((p>>i)&1)<<j for j,i in enumerate(E)) for p in P)
        if len(canonical(rho))!=size:
            continue
        small=tuple(sum(((chord[e]>>i)&1)<<j for j,i in enumerate(E)) for e in J)
        Q=tuple(J[j] for j in basis_indices(small))
        if len(Q)!=size:
            continue
        transfer=tuple(sum(((chord[e]>>i)&1)<<j for j,i in enumerate(E)) for e in Q)
        break
    else:
        if size!=1:
            return None
        E=Q=transfer=()
        assert all((v&P[0])==0 for v in chord.values())
    records={}
    for a in range(1<<size):
        for b in range(1<<size):
            color=[0]*len(cols)
            f,g=image(P,a),image(P,b)
            for e in J:
                if e not in Q:
                    color[e]=1
                    f^=chord[e]
            want=sum((1^((f>>i)&1))<<j for j,i in enumerate(E))
            first=solve(transfer,want)
            for j,e in enumerate(Q):
                flag=(first>>j)&1
                color[e]=2+flag
                g^=chord[e]
                if flag:
                    f^=chord[e]
            for j,e in enumerate(B):
                color[e]=((f>>j)&1)|(((g>>j)&1)<<1)
            score=0
            for v,(x,y) in zip(color,tags):
                if v&1:
                    score^=x
                if v&2:
                    score^=y
            records[a,b]=(tuple(color),score)
    return ('transparent' if E else 'ordinary',records)
