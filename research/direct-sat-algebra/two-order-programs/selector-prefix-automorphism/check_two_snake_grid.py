"""Proper colorings on perpendicular snakes coupled by private orientation bits."""
from itertools import combinations, product
from orbit_solver import solve


def instance(height,width):
    n=height*width
    row=tuple(i*width+j for i in range(height) for j in
              (range(width) if i%2==0 else reversed(range(width))))
    col=tuple(i*width+j for j in range(width) for i in
              (range(height) if j%2==0 else reversed(range(height))))
    clauses=[]
    def names(site,part):
        return tuple(12*site+3*part+c+1 for c in range(3))
    def color_step(site,prev,part):
        values=names(site,part)
        clauses.append(values)
        clauses.extend((-a,-b) for a,b in combinations(values,2))
        if prev is not None:
            clauses.extend((-a,-b) for a,b in zip(names(prev,part),values))
    for k,s in enumerate(row):
        color_step(s,row[k-1] if k else None,3)
        for x,u,v,w in zip(*(names(s,p) for p in range(4))):
            clauses.extend([(-u,w),(-v,w),(u,v,-w),(x,-u),(-x,-v)])
    cut=len(clauses)
    for k,s in enumerate(col):
        color_step(s,col[k-1] if k else None,0)
    return 12*n,clauses,cut,row,col


def witness(w,x):
    word=0
    for s,(a,b) in enumerate(zip(w,x)):
        A,B=1<<a,1<<b
        word|=(B|((A&B)<<3)|((A&~B)<<6)|(A<<9))<<(12*s)
    return word


def accepts(clauses,word):
    return all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)


if __name__=="__main__":
    for height,width in [(1,2),(2,2)]:
        n,clauses,cut,row,col=instance(height,width)
        paths=lambda order:[v for v in product(range(3),repeat=len(row))
                            if all(v[i]!=v[j] for i,j in zip(order,order[1:]))]
        for w in paths(row):
            for x in paths(col):
                assert accepts(clauses,witness(w,x))
        outputs=solve(n,clauses,state_cap=1<<15)
        assert outputs["status"]=="sat" and accepts(clauses,outputs["witness"])
        assert outputs["counts"][cut-1]==1
        print(height,width,max(outputs["counts"]),outputs["counts"][cut-1])
