"""Evaluate a physical routing using its total fourth exterior form."""
from fractions import Fraction
from itertools import combinations
from native_paired_rows import prepare, insert, reduce_row

def indices(mask):
    while mask:
        bit=mask & -mask
        yield bit.bit_length()-1
        mask^=bit

def sign(left,right):
    return -1 if sum((right&((1<<i)-1)).bit_count() for i in indices(left))%2 else 1

def add(out,key,v):
    if not v:return
    out[key]=out.get(key,0)+v
    if not out[key]:del out[key]

def wedge(left,right,scale=1):
    out={}
    for a,x in left.items():
        for b,y in right.items():
            if not a&b:add(out,a|b,scale*x*y*sign(a,b))
    return out

def twoform(menu,d):
    out={}
    for _,(a,b) in menu:
        for i,j in combinations(range(d),2):
            add(out,(1<<i)|(1<<j),a[i]*b[j]-a[j]*b[i])
    return out

def pfaffian(a):
    a=[list(v) for v in a];result=1
    while a:
        j=next((j for j in range(1,len(a)) if a[0][j]),None)
        if j is None:return 0
        if j!=1:
            a[j],a[1]=a[1],a[j]
            for row in a:row[j],row[1]=row[1],row[j]
            result=-result
        p=a[0][1];result*=p
        a=[[a[i][j]-Fraction(a[0][i]*a[1][j]-a[0][j]*a[1][i],p)
            for j in range(2,len(a))] for i in range(2,len(a))]
    return result

def evaluate(opts,fixed):
    n=len(opts);base={}
    for i,j in fixed.items():
        for v in opts[i][j][1]:
            if not insert(v,base):return False
    free=[i for i in range(2*n) if i not in base]
    def project(v):
        row=reduce_row(v,base)
        return [row[j] for j in free]
    pending=[[(x,(project(a),project(b))) for x,(a,b) in q]
             for i,q in enumerate(opts) if i not in fixed]
    d=len(free);omega={}
    for q in pending:
        c=twoform(q,d)
        for k,v in wedge(c,c).items():add(omega,k,v)
    contractions={}
    for mask,v in omega.items():
        for i in indices(mask):
            rest=mask^(1<<i)
            row=contractions.setdefault(rest,[0]*d)
            row[i]=sign(rest,1<<i)*v
    support={}
    for row in contractions.values():insert(row,support)
    piv=sorted(support)
    for i in reversed(piv):
        for j in piv:
            if j<i and support[j][i]:
                a=support[j][i]
                support[j]=[x-a*y for x,y in zip(support[j],support[i])]
    rest=[i for i in range(d) if i not in support]
    def rebase(v):
        coeff=[v[i] for i in piv]
        return coeff+[v[i]-sum(v[j]*support[j][i] for j in piv) for i in rest]
    aform={}
    for q in pending:
        q1=[(x,(rebase(a),rebase(b))) for x,(a,b) in q]
        for k,v in twoform(q1,d).items():add(aform,k,v)
    a=[[0]*d for _ in range(d)]
    for key,v in aform.items():
        i,j=indices(key);a[i][j]=v;a[j][i]=-v
    omega_small={}
    for subset in combinations(range(len(piv)),4):
        v=omega.get(sum(1<<piv[j] for j in subset),0)
        if v:omega_small[sum(1<<j for j in subset)]=v
    terms={0:1};power={0:1}
    for j in range(1,len(piv)//4+1):
        power=wedge(power,omega_small,Fraction(-1,2*j))
        if not power:break
        terms.update(power)
    full=(1<<d)-1;total=0
    for u,c in terms.items():
        comp=full^u;cols=list(indices(comp))
        minor=[[a[i][j] for j in cols] for i in cols]
        total+=c*sign(u,comp)*pfaffian(minor)
    return abs(total)

def solve(feedback,menus,r,s):
    opts=prepare(feedback,menus,r,s)
    if opts is None:return None
    if not opts:return tuple(m[0] for m in menus)
    fixed={}
    if not evaluate(opts,fixed):return None
    for i,q in enumerate(opts):
        for j in range(len(q)):
            fixed[i]=j
            if evaluate(opts,fixed):break
        else:raise AssertionError('no actual option extends the recovered prefix')
    return tuple(opts[i][j][0] for i,j in fixed.items())
