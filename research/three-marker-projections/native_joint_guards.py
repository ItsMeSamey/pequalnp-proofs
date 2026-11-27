"""Exact rational algebra for correlated choices in multiple native guards."""
from fractions import Fraction
from native_net_defect import indices,sign,add,wedge,pfaffian
from native_paired_rows import prepare,insert,reduce_row

def assemble(guards):
    sites={};offset=0
    for feedback,menus,r,s in guards:
        opts=prepare(feedback,[q for _,q in menus],r,s)
        if opts is None:raise AssertionError('dependent forced sums')
        if not opts:continue
        for (label,shifts),menu in zip(menus,opts):
            sites.setdefault(label,[]).append((offset,[ab for _,ab in menu]))
        offset+=2*len(opts)
    for group in sites.values():
        if len({len(q)for _,q in group})!=1:raise ValueError('mismatched common menu')
    return sites,offset

def evaluate(assembled,fixed,measure=False):
    sites,dimension=assembled;base={}
    def embed(start,v):
        return [0]*start+list(v)+[0]*(dimension-start-len(v))
    for i,choice in fixed.items():
        for start,menu in sites[i]:
            for v in menu[choice]:
                if not insert(embed(start,v),base):return 0,None
    free=[i for i in range(dimension)if i not in base];d=len(free)
    def coordinates(start,v):
        v=reduce_row(embed(start,v),base)
        return {1<<j:v[i]for j,i in enumerate(free)if v[i]}
    quadratic={};defect={}
    for label,group in sites.items():
        if label in fixed:continue
        count=len(group[0][1]);local={}
        for choice in range(count):
            term={0:1}
            for start,menu in group:
                a,b=menu[choice]
                biv=wedge(coordinates(start,a),coordinates(start,b));biv[0]=1
                term=wedge(term,biv)
            for k,v in term.items():add(local,k,Fraction(v,count))
        assert local.pop(0)==1
        power=local.copy()
        for j in range(1,2*len(group)+1):
            if not power:break
            for k,v in power.items():
                add(quadratic if k.bit_count()==2 else defect,k,Fraction((-1)**(j+1),j)*v)
            if j<2*len(group):power=wedge(power,local)
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

def solve(guards):
    system=assemble(guards)
    if not evaluate(system,{})[0]:return None
    fixed={}
    for label,group in system[0].items():
        for a in range(len(group[0][1])):
            fixed[label]=a
            if evaluate(system,fixed)[0]:break
        else:raise AssertionError('a common physical choice was lost')
    for _,menus,_,_ in guards:
        for label,_ in menus:fixed.setdefault(label,0)
    return fixed
