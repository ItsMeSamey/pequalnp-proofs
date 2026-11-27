from native_sat_guards import encode
from native_joint_guards import assemble,evaluate
from native_paired_rows import prepare,insert
from native_net_defect import twoform,indices

def variation(guard):
    p,menus,r,s=guard
    opts=prepare(p,[q for _,q in menus],r,s)
    d=2*len(opts);basis={};ranks=[]
    for q in opts:
        a=twoform(q[:1],d);b=twoform(q[1:],d);mat=[[0]*d for _ in range(d)]
        for k in a.keys()|b.keys():
            i,j=indices(k);mat[i][j]=a.get(k,0)-b.get(k,0);mat[j][i]=-mat[i][j]
        local={}
        for row in mat:insert(row,local);insert(row,basis)
        ranks.append(len(local))
    return ranks,len(basis)

def measure(f):
    g,_=encode(f)
    return len(g),evaluate(assemble(g),{},measure=True)[1]

if __name__=='__main__':
    for n in (2,3,4,6,8):
        for sign in (-1,1):
            f=[[1]]+[[-i,i+1] for i in range(1,n)]+[[sign*n]]
            assert measure(f)==(2*n+1,8*n)
        print(n,'variables; both chain signs have support',8*n)
    g,_=encode([[1],[-1,2],[-2]])
    for h in g:
        k=len(h[1]);assert variation(h)==([2]*k,2*k)
    for m in (1,2,5,10):
        assert measure([[2*i+1,2*i+2]for i in range(m)])==(m,0)
    print('binary disjoint clauses have zero support, tested through ten clauses')
