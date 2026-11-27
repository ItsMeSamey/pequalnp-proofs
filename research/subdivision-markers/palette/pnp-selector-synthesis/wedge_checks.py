from wedge_path import solve,wedge
from frontier import basis
from recognizer import tag_at,bit_indices
from random import Random
def direct(cols):
    d=max((k.bit_length() for k,b in cols),default=0)
    generators=[]
    relations=[]
    for g in range(1<<(2*d)):
        pivots={}
        local=[]
        for i,(k,b) in enumerate(cols):
            if tag_at(g,k,d)!=b: continue
            trace=1<<i
            while k:
                lead=k.bit_length()-1
                if lead not in pivots:
                    pivots[lead]=(k,trace)
                    break
                v,t=pivots[lead]
                k ^= v
                trace ^= t
            if not k: local.append(trace)
        generators.extend(wedge(u,v) for i,u in enumerate(local) for v in local[:i])
        relations.extend(local)
    return basis(generators),basis(relations)

def check(cols):
    reps,w=solve(cols)
    expected,L=direct(cols)
    assert basis(z for u,v,z in reps)==expected
    for u,v,z in reps:
        assert wedge(u,v)==z
        d=max((k.bit_length() for k,b in cols),default=0)
        assert any(all(tag_at(g,cols[i][0],d)==cols[i][1] for i in bit_indices(u|v)) for g in range(1<<(2*d)))
    return reps,w,len(L)
def main():
    rng=Random(413)
    for _ in range(24): check([(rng.randrange(4),rng.randrange(4)) for i in range(6)])
    assert check([(1,0),(1,0),(1,1),(1,1)])[0]==[]
    assert len(check([(1,0),(1,0),(2,1),(2,1)])[0])==1
    data=[17,23,24,28,35,38,40,47,62,64,74,83,90,92,100,104,109]
    cols=[(x>>4,(x>>2)&3) for x in data]
    reps,w,r=check(cols)
    def height(u):
        h=0
        for i in bit_indices(u): h ^= data[i]&3
        return h
    assert all(not (height(u) and height(v) and height(u)!=height(v)) for u,v,z in reps)
    print('27 exact wedge spaces passed; rank7 control: W dimension',len(reps),'r',r,'width',w)
if __name__=='__main__':main()
