"""Scalar, typed accepted/trial hash-query evaluator on the original variables."""
from dataclasses import dataclass
from itertools import product
from math import comb,isqrt
from packet_layout import SourcePlan, rounded_power
from source_cnf_driver import field
from variable_packet_machine import solve


def xor_insert(terms,m):
    if m in terms:terms.remove(m)
    else:terms.add(m)


def clause_violation(n,c):
    if any(not 1<=abs(z)<=n for z in c):raise ValueError('invalid literal')
    c=set(c)
    if any(-z in c for z in c):return set()
    base=sum(1<<(-z-1) for z in c if z<0)
    terms={base}
    for z in c:
        if z>0:terms.update({a|1<<(z-1) for a in terms})
    return terms


def row_polys(n,clauses,checks,trial):
    pieces=[clause_violation(n,c) for c in clauses]
    rows=[]
    for check in list(checks)+([] if trial is None else [trial]):
        terms=set()
        for clause_id,enabled in check:
            if not 0<=clause_id<len(pieces):raise ValueError('invalid clause index')
            if enabled:terms.symmetric_difference_update(pieces[clause_id])
        rows.append(tuple(sorted(terms)))
    return tuple(rows)


def scope(row):
    mask=0
    for t in row:mask|=t
    return mask


def decode(pool,d,index):
    if index>=comb(len(pool),d):return None
    out=[]
    for j,item in enumerate(pool):
        if not d:break
        count=comb(len(pool)-1-j,d-1)
        if index<count:out.append(item);d-=1
        else:index-=count
    return out


@dataclass(frozen=True)
class Port:
    entries:tuple
    chosen:int
    width:int


@dataclass(frozen=True)
class QueryVertex:
    birth:int
    extension:int
    ports:tuple
    rows:tuple
    variables:tuple
    test:bool

    def word(self,bits):
        mod=1<<self.birth
        value=1;pos=0;chosen={}
        for port in self.ports:
            ix=sum(bits[pos+j]<<j for j in range(port.width));pos+=port.width
            subset=decode(port.entries,port.chosen,ix)
            if subset is None:return (0,)*self.extension
            for i,v in subset:chosen[i]=chosen.get(i,0)|(1<<v)
        if self.test:
            for i,row in self.rows:
                s=chosen.get(i,0);t=s;c=0
                while True:
                    valid=1^(sum((x&t)==x for x in row)&1)
                    c+=(-1 if (s^t).bit_count()&1 else 1)*valid
                    if not t:break
                    t=(t-1)&s
                value=value*c%mod
        else:
            used=0
            for s in chosen.values():used|=s
            value=pow(2,sum(not((used>>v)&1) for v in self.variables),mod)
        return (value,)+(0,)*(self.extension-1)


def count_system(n,rows,degree):
    if n<0 or degree<0:raise ValueError('invalid input dimensions')
    if any(t<0 or t.bit_length()>n or t.bit_count()>degree for row in rows for t in row):
        raise ValueError('out of range monomial or degree')
    lam=max(1,(max(2,n)-1).bit_length())
    nu=max(1,(lam-1).bit_length());size=max(2,n*nu)
    p=n+1;mod=1<<p; f=field(size)
    heavydeg=[sum((scope(row)>>v)&1 for row in rows) for v in range(n)]
    ceilroot=isqrt(lam-1)+1
    threshold=max(1,(sum(heavydeg)+n-1)//max(1,n))*ceilroot
    heavy=[v for v,d in enumerate(heavydeg) if d>threshold]
    hmask=sum(1<<v for v in heavy)
    free=[v for v in range(n) if not(hmask>>v&1)]
    J=isqrt(isqrt(max(n,1)))
    if J**4<n:J+=1
    answer=0
    for assignment in range(1<<len(heavy)):
        one=sum(((assignment>>i)&1)<<v for i,v in enumerate(heavy))
        local=[]
        for row in rows:
            simplified=set()
            for t in row:
                if not(t&hmask&~one):xor_insert(simplified,t&~hmask)
            if simplified:local.append(tuple(sorted(simplified)))
        if (0,) in local:continue
        if not local:answer=(answer+(1<<len(free)))%mod;continue
        tg=[list(range(g,len(local),J)) for g in range(J)]
        vg=[free[h::J] for h in range(J)]
        pools=[tuple((i,v) for i in group for v in vs if scope(local[i])>>v&1)
               for group in tg for vs in vg]
        ds=[0]*len(pools)
        def visit(j,room):
            nonlocal answer
            if j<len(pools):
                for d in range(min(room,len(pools[j]))+1):
                    ds[j]=d;visit(j+1,room-d)
                return
            tp=[[] for _ in tg];vp=[[] for _ in vg]
            te=[[] for _ in tg];ve=[[] for _ in vg];m=0
            for z,(pool,d) in enumerate(zip(pools,ds)):
                g,h=divmod(z,J);w=(comb(len(pool),d)-1).bit_length()
                obj=Port(pool,d,w);tp[g].append(obj);vp[h].append(obj)
                te[g].extend(range(m,m+w));ve[h].extend(range(m,m+w));m+=w
            left=[(QueryVertex(p,len(f),tuple(tp[g]),tuple((i,local[i]) for i in tg[g]),(),True),
                   tuple(te[g])) for g in range(J)]
            right=[(QueryVertex(p,len(f),tuple(vp[h]),(),tuple(vg[h]),False),
                    tuple(ve[h])) for h in range(J)]
            plan=SourcePlan(size,m,p)
            if max(map(len,te+ve),default=0)>rounded_power(size):plan=lambda *args:None
            result=solve((left,right),m,p,f,1,0,plan)
            assert not any(result[1:])
            answer=(answer+result[0])%mod
        visit(0,degree*(len(local)+n))
    return answer


def count_query(n,clauses,checks,trial=None):
    """checks and optional trial contain (zero-based clause ID, Boolean coefficient) entries."""
    return count_system(n,row_polys(n,clauses,checks,trial),max(map(len,clauses),default=0))
