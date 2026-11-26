"""Tiny full binary-layout/Hasse-jet counter, with Q=r=R=2 on four bits."""
from itertools import product
from math import comb

def pack(a,b=0): return a%32+32*(b%32)
def add(x,y): return pack(x%32+y%32,x//32+y//32)
def neg(x): return pack(-(x%32),-(x//32))
def mul(x,y):
    a,b,c,d=x%32,x//32,y%32,y//32
    return pack(a*c-b*d,a*d+b*c-b*d)
def inv(x):
    a,b=x%32,x//32
    k=pow((a*a-a*b+b*b)%32,-1,32)
    return pack(k*(a-b),-k*b)
def ring_sum(xs):
    a=0
    for x in xs: a=add(a,x)
    return a
def power(x,n):
    ans=1
    for _ in range(n): ans=mul(ans,x)
    return ans

nodes=(1,32)
def replacement(v,target):
    const=[0]*4
    slope=[0]*4
    for a,d in product(range(4),repeat=2):
        same=all(sorted(((a>>i)&1,(d>>i)&1))==sorted(((v>>i)&1,(target>>i)&1)) for i in range(2))
        C=int(same and (v^target)==3)
        M=int((v,target)==(a,d))-C
        const[a]=add(const[a],pack(C+M))
        if M:
            bad=[i for i in range(2) if (a^target)>>i&1]
            assert len(bad)<=1
            if bad: slope[a]=add(slope[a],mul(pack(-M),inv(nodes[bad[0]])))
    assert const==[int(i==v) for i in range(4)]
    return const,slope

def scalar(row,x):
    return ring_sum(v for i,v in enumerate(row) if x>>i&1)
def pmul(f,g,J,L=5):
    out={}
    for (i,j),a in f.items():
        for (k,l),b in g.items():
            if i+k<J and j+l<L:
                idx=(i+k,j+l)
                out[idx]=add(out.get(idx,0),mul(a,b))
    return out
def psubone(f):
    vals={key:neg(v) for key,v in f.items()}
    vals[0,0]=add(vals.get((0,0),0),1)
    return vals
def padd(f,g):
    out=f.copy()
    for key,v in g.items(): out[key]=add(out.get(key,0),v)
    return out
def recover(jets,J):
    size=len(nodes)*J
    m=[]
    for t,values in zip(nodes,jets):
        for j,val in enumerate(values):
            m.append([mul(pack(comb(i,j)),power(t,i-j)) if i>=j else 0 for i in range(size)]+[val])
    for i in range(size):
        k=next(k for k in range(i,size) if (m[k][i]%2) or ((m[k][i]//32)%2))
        m[k],m[i]=m[i],m[k]
        div=inv(m[i][i])
        m[i]=[mul(v,div) for v in m[i]]
        for k in range(size):
            if k==i: continue
            fac=m[k][i]
            m[k]=[add(a,neg(mul(fac,b))) for a,b in zip(m[k],m[i])]
    return m[0][-1]

def count(formula):
    # Each clause includes its destination schedule and signed variable ids.
    J=1+sum(len(c) for _,c in formula)//2
    jets=[]
    for t,node in enumerate(nodes):
        masks=[sum(1<<i for i in range(4) if (i>>t)&1==g) for g in range(2)]
        groups=[[] for _ in range(2)]
        for d,cl in formula:
            rows=[]
            for var,negative in cl:
                base,slope=replacement(var,d)
                at=[add(a,mul(node,b)) for a,b in zip(base,slope)]
                rows.append((at,slope,negative))
            groups[(d>>t)&1].append(rows)
        ans=[0]*J
        for labels in product(range(2),repeat=2):
            choices=[[x for x in range(16) if x&~mask==0 and x.bit_count()%2==label] for mask,label in zip(masks,labels)]
            reps=[min(xs) for xs in choices]
            for E in range(16):
                if E.bit_count()>J-1+4: continue
                U=E
                while True:
                    total={(0,0):1}
                    for g,grp in enumerate(groups):
                        part={}
                        for x in choices[g]:
                            if E&masks[g]&~x: continue
                            local={(0,0):1}
                            for rows in grp:
                                violated={(0,0):1}
                                for at,slope,negative in rows:
                                    c=scalar(at,x|reps[1-g])
                                    delta=add(scalar(at,U&masks[1-g]),neg(scalar(at,reps[1-g])))
                                    sub={(0,0):c,(0,1):delta,(1,0):scalar(slope,U)}
                                    violated=pmul(violated,sub if negative else psubone(sub),J)
                                local=pmul(local,psubone(violated),J)
                            part=padd(part,local)
                        total=pmul(total,part,J)
                    coeff=pack((-1)**((E^U).bit_count()))
                    for (j,_),v in total.items():
                        ans[j]=add(ans[j],mul(coeff,v))
                    if U==0: break
                    U=(U-1)&E
        jets.append(ans)
    return recover(jets,J)


def brute(f):
    return sum(all(any(((x>>v)&1)^negated for v,negated in cl) for _,cl in f) for x in range(16))

forms=[[],[(3,[(0,False)])],[(3,[(0,False)]),(2,[(0,True)])],
       [(3,[(0,False),(1,True)]),(1,[(2,False),(0,False)]),(0,[(3,True),(2,False)])],
       [(3,[(0,True),(2,True),(1,False)]),(2,[(1,True),(3,False)]),(0,[(3,False)]),(1,[(2,False)])]]
for form in forms:
    actual=count(form)
    assert actual==brute(form),(actual,brute(form))
    print("count",actual)

# Six repeated row uses activate the discrepancy cutoff at V^5.
repeated=[(3,[(0,False)])]*6+[(0,[(3,True)])]
assert count(repeated)==brute(repeated)==4
print("six-use discrepancy case",4)
