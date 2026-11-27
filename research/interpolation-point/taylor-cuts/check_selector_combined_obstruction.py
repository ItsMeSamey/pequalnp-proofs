"""Check simultaneous failure of the affine two-level and literal-anchored tests."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json
import numpy as np
from check_dummy_layer_corrections import matchings,null


def source():
    edges=[]
    for i in range(4):
        module=range(4*i,4*i+4)
        edges.extend(combinations(module,2))
        edges.extend((v,16+i//2) for v in module)
    marked=[(0,8),(1,12),(4,9),(5,13)]
    edges=sorted(edges+marked+[(16,17)])
    return edges,np.array([int(e in marked) for e in edges],dtype=np.int16)


def rational_rank(rows):
    pivots={}
    for vec in rows:
        row=list(map(Fraction,map(int,vec)))
        for p,w in sorted(pivots.items()):
            if row[p]:
                c=row[p]
                row=[a-c*b for a,b in zip(row,w)]
        first=next((i for i,v in enumerate(row) if v),None)
        if first is not None:
            pivots[first]=[v/row[first] for v in row]
    return len(pivots)


def check():
    edges,w=source()
    X=matchings(edges,18,9)
    assert len(X)==442 and set(X@w)=={0,1,3,4}
    def affine(M):
        return np.column_stack((np.ones(len(M),dtype=np.int16),M))
    x=affine(X)
    flag=(X@w%3==1).astype(np.int16)
    A=np.column_stack((x,flag)).astype(np.int64)
    gram=A.T@A
    assert rational_rank(gram[:-1,:-1])==28 and rational_rank(gram)==29
    data=json.loads(Path(__file__).with_name("selector_combined_obstruction.json").read_text())
    Y=np.zeros((len(data),len(edges)),dtype=np.int16)
    z=np.array([c for c,_ in data],dtype=np.int16)
    for j,(c,ids) in enumerate(data):
        assert c in (1,2) and len(ids)==8 and all(0<=i<len(edges) for i in ids)
        assert len({v for i in ids for v in edges[i]})==16
        Y[j,ids]=1
    y=affine(Y)
    for i in range(len(edges)):
        for val in (0,1):
            identities=null(x[X[:,i]==val])
            moment=(z*(Y[:,i]==val))@y%3
            assert not np.any(moment@identities.T%3)
    assert z@((1-((Y@w-2)%3)**2)%3)%3==1
    print("442 perfect matchings; real ranks 28 and 29;",
          len(z),"signed near-perfect witnesses; 90 literal conditions; residual 1")


if __name__=="__main__":
    check()
