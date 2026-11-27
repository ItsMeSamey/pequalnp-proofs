"""Nearest common Boolean witness when every total variation has rank at most four."""
from fractions import Fraction
from native_net_defect import indices,sign,add,wedge,pfaffian,twoform
from native_paired_rows import insert
from native_joint_guards import assemble

def top(quadratic,defect,d,measure=False):
    contractions={}
    for mask,v in defect.items():
        for i in indices(mask):
            rest=mask^(1<<i)
            row=contractions.setdefault(rest,[0]*d)
            row[i]=sign(rest,1<<i)*v
    support={}
    for row in contractions.values():insert(row,support)
    piv=sorted(support)
    if measure:return None,len(piv)
    for i in reversed(piv):
        for j in piv:
            if j<i and support[j][i]:
                a=support[j][i]
                support[j]=[x-a*y for x,y in zip(support[j],support[i])]
    rest=[i for i in range(d)if i not in support]
    def rebase_unit(i):
        if i in support:
            y={1<<piv.index(i):1}
            y.update({1<<(len(piv)+j):-support[i][k] for j,k in enumerate(rest)if support[i][k]})
            return y
        return {1<<(len(piv)+rest.index(i)):1}
    units=[rebase_unit(i)for i in range(d)]
    mat=[[0]*d for _ in range(d)]
    for k,v in quadratic.items():
        i,j=indices(k)
        for q,z in wedge(units[i],units[j],v).items():
            a,b=indices(q);mat[a][b]+=z;mat[b][a]-=z
    compressed={}
    pos={i:j for j,i in enumerate(piv)}
    for k,v in defect.items():
        ind=list(indices(k))
        if all(i in pos for i in ind):compressed[sum(1<<pos[i]for i in ind)]=v
    terms={0:1};power={0:1}
    for j in range(1,len(piv)//4+1):
        power=wedge(power,compressed,Fraction(1,j))
        if not power:break
        for k,v in power.items():add(terms,k,v)
    total=0;full=(1<<d)-1
    for u,v in terms.items():
        comp=full^u;k=list(indices(comp))
        total+=v*sign(u,comp)*pfaffian([[mat[i][j]for j in k]for i in k])
    return abs(total),len(piv)

def compile_binary(guards):
    sites,d=assemble(guards);base={};delta={};squares={}
    for i,group in sites.items():
        a={};b={}
        for off,q in group:
            if len(q) not in (1,2):raise ValueError('requires Boolean or constant controls')
            for table,j in ((a,0),(b,len(q)-1)):
                for k,v in twoform([(j,q[j])],len(q[j][0])).items():add(table,k<<off,v)
        for k,v in a.items():add(base,k,v);add(b,k,-v)
        if len(group[0][1])==1:continue
        bb=wedge(b,b)
        if wedge(bb,b):raise ValueError('total selector variation has rank greater than four')
        delta[i]=b
        for k,v in bb.items():add(squares,k,v)
    return sites,d,base,delta,squares

def solve(guards):
    sites,d,base,delta,squares=compile_binary(guards)
    cap=2**len(delta)*3**sum(len(p) for p,_,_,_ in guards)+1
    p=Fraction(1,cap+1)
    defect={k:v*p*(1-p)/2 for k,v in squares.items()}
    word={i:0 for i in sites}
    def score():
        a=base.copy()
        for i,b in delta.items():
            prob=(1-p) if word[i] else p
            for k,v in b.items():add(a,k,v*prob)
        return top(a,defect,d)[0]
    def accepted():
        for feedback,menu,r,s in guards:
            i=r;seen=set()
            while i not in seen and i!=s:
                seen.add(i);j=i//3
                label,q=menu[j];shift=q[word.get(label,0)]
                i=feedback[3*j+(i%3+shift)%3]
            if i!=s:return False
        return True
    if not score():return None
    for _ in range(len(delta)+1):
        if accepted():
            for _,menu,_,_ in guards:
                for i,_ in menu:word.setdefault(i,0)
            return word
        best=-1;chosen=None
        for i in delta:
            word[i]^=1;z=score();word[i]^=1
            if z>best:best=z;chosen=i
        if chosen is None:raise AssertionError('nonzero score without a live option')
        word[chosen]^=1
    raise AssertionError('distance to a witness failed to decrease')
