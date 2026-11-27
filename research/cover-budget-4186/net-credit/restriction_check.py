"""Replay false projection, including output remapping and false-marker bypass."""
from itertools import product
from net import build


def project(n,gates,output,removed):
    renaming=[None if x==removed else x-(x>removed) for x in range(n)]
    result=[]
    for op,a,b in gates:
        x,y=renaming[a],renaming[b]
        if x is None or y is None:
            renaming.append(None if op=="and" else y if x is None else x)
        else:
            renaming.append(n-1+len(result))
            result.append((op,x,y))
    return result, renaming[output] if output<len(renaming) else None


def eval_at(x,gates,output):
    w=list(x)
    for op,a,b in gates:
        w.append((w[a] and w[b]) if op=="and" else (w[a] or w[b]))
    return w[output] if output is not None and output<len(w) else False


def verify(n,gates,output,i):
    shortened,new=project(n,gates,output,i)
    for x in product((False,True),repeat=n-1):
        old=x[:i]+(False,)+x[i:]
        assert eval_at(x,shortened,new)==eval_at(old,gates,output)
    return len(gates)-len(shortened),new


for p,d,z in ((1,1,1),(3,1,2),(2,2,2)):
    n,gates,o,edges,classes,wires,children=build(p,d,z)
    for group in classes:
        for i in group:
            lost,out=verify(n,gates,o,i)
            assert lost>=1 and out is not None
assert verify(2,[("or",0,1)],2,0)==(1,0)
assert verify(3,[("and",0,1),("or",3,2)],4,0)==(2,1)
assert verify(2,[("or",0,1)],5,0)==(1,None)
assert verify(2,[("and",0,0)],0,0)==(1,None)
assert verify(2,[("or",0,0)],2,0)==(1,None)
print("Restriction truth tables verified, including reindexed raw, missing and constant-false outputs")
