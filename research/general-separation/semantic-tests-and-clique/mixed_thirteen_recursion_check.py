"""Independent raw regressions for mixed 13-state two-readout solvers."""
from itertools import product
from random import Random
from mixed_thirteen_star_check import raw
from general_fourteen_check import verify

DOUBLE = 4095 | (1<<12)  # At 11 only defect 00 is allowed.
EQUAL = 65535 ^ (1<<13) ^ (1<<14)


def edge(rows,i,j):
    rows[i] ^= 1<<j
    rows[j] ^= 1<<i


def pair_chain(stages,yes):
    n=2*stages
    rows=[0]*n
    tables=[(i,i+1,DOUBLE) for i in range(0,n,2)]
    c=0
    for i in range(n-2):
        edge(rows,i,i+2)
        c ^= 1<<i
        c ^= 1<<(i+2)  # Compensation for the incoming fixed previous site.
    if not yes:
        c ^= 1<<(n-1)
    return rows,c,tables,[1,2]+[0]*(n-2),3


def star_chain(stages,yes):
    n=4*stages
    rows=[0]*n
    tables=[]
    c=0
    for base in range(0,n,4):
        h,i,j,k=range(base,base+4)
        tables.extend((v,h,DOUBLE) for v in (i,j,k))
        edge(rows,i,j)
        edge(rows,j,k)
        c ^= 1<<i
        if base+4<n:
            # The final satellite equation imposes new_h=1. The old hub
            # equation imposes new_mark=1. Both become next-stage readouts.
            new_h,new_mark=base+4,base+5
            edge(rows,k,new_h)
            edge(rows,h,new_mark)
            c ^= (1<<h)|(1<<new_h)|(1<<new_mark)
        else:
            c ^= 1<<k
            if not yes:
                c ^= 1<<h
    return rows,c,tables,[1,2]+[0]*(n-2),3


def ordinary_hub(extra,yes):
    # h=0 has strict satellites 1,2,3; 4 is its ordinary-component partner.
    n=7
    rows=[0]*n
    tables=[(i,0,DOUBLE) for i in (1,2,3)]+[(0,4,EQUAL),(5,6,DOUBLE)]
    edge(rows,1,2)
    edge(rows,2,3)
    edge(rows,3,4)
    if extra:
        tables.append((4,5,DOUBLE))
    if yes:
        edge(rows,0,5)
    return rows,2,tables,[1,2,0,0,0,0,0],3


def expected(data):
    rows,c,tables,labels,target=data
    words=[]
    for w in range(1<<len(rows)):
        read=0
        for i,b in enumerate(labels):
            if w>>i&1:
                read ^= b
        if read==target and raw(rows,c,tables,w,0):
            words.append(w)
    return words


def fixtures():
    for stages in (1,2,3,4,5):
        for yes in (False,True):
            yield f"pair chain {stages} {yes}",pair_chain(stages,yes),yes
    for stages in (1,2,3):
        for yes in (False,True):
            yield f"star chain {stages} {yes}",star_chain(stages,yes),yes
    for extra,yes in product((False,True),repeat=2):
        yield f"two-site ordinary hub {extra} {yes}",ordinary_hub(extra,yes),extra or yes


def relabel(data,rng):
    rows,c,edges,labels,target=data
    n=len(rows)
    permutation=list(range(n))
    rng.shuffle(permutation)
    def remap(word):
        return sum(((word>>i)&1)<<permutation[i] for i in range(n))
    new_rows=[0]*n
    new_labels=[0]*n
    for i,j in enumerate(permutation):
        new_rows[j]=remap(rows[i])
        new_labels[j]=labels[i]
    new_edges=[]
    new_c=remap(c)
    for i,j,table in edges:
        if rng.randrange(2):
            swap=lambda v: ((v&1)<<1)|(v>>1)
            table=sum(((table>>(4*s+d))&1)<<(4*swap(s)+swap(d))
                      for s,d in product(range(4),repeat=2))
            i,j=j,i
        shift=rng.randrange(4)
        table=sum(((table>>(4*s+d))&1)<<(4*s+(d^shift))
                  for s,d in product(range(4),repeat=2))
        new_c ^= ((shift&1)<<permutation[i]) | ((shift>>1)<<permutation[j])
        new_edges.append((permutation[i],permutation[j],table))
    rng.shuffle(new_edges)
    return new_rows,new_c,new_edges,new_labels,target


def measured(solver,data):
    import sys
    from collections import Counter
    calls=Counter()
    depth=0
    maximum=0
    def hook(frame,event,arg):
        nonlocal depth,maximum
        if frame.f_globals.get("__name__")!=solver.__module__:
            return
        name=frame.f_code.co_name
        if name not in ("stage","star","two_fixed","one"):
            return
        if event=="call":
            calls[name]+=1
            if name=="stage":
                depth+=1
                maximum=max(depth,maximum)
        elif event=="return" and name=="stage":
            depth-=1
    previous=sys.getprofile()
    sys.setprofile(hook)
    try:
        answer=solver(*data)
    finally:
        sys.setprofile(previous)
    return answer,dict(calls),maximum


def run(solver=None):
    checked=0
    rng=Random(456991)
    cases=list(fixtures())
    cases.extend((name+" permuted",relabel(data,rng),want) for name,data,want in list(cases))
    for name,data,want in cases:
        words=expected(data)
        assert bool(words)==want,(name,words)
        if solver is not None:
            ans,calls,depth=measured(solver,data)
            if "permuted" not in name and ("chain 5" in name or "star chain 3" in name or
                                           "ordinary hub" in name):
                print(name,calls,"max stage depth",depth)
            assert (ans is not None)==want,name
            if ans is not None:
                w,defects=ans
                assert w in words and verify(data[0],data[1],data[2],w,defects),name
        checked+=1
    print("structured fixtures checked",checked)


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--solver",action="store_true")
    if parser.parse_args().solver:
        from mixed_thirteen_solver import solve,Model,View
        for c,expected_word in ((0,3),(2,None)):
            view=View(Model([0,0],c,[(0,1,DOUBLE)],0),2,1)
            assert view.singletons==2 and not view.releases[1]
            assert view.one([(2,1)])==expected_word
        run(solve)
    else:
        run()
