"""Compile signed clauses to one open native input-to-output query."""
from itertools import product


def compile_open(n,clauses):
    if not clauses or any(not 1<=len(c)<=3 for c in clauses):
        raise ValueError("expected nonempty clauses of size one through three")
    ng=0;succ={};occupied=set()
    def gate():
        nonlocal ng
        x=3*ng;ng+=1
        return x
    def wire(out,inp):
        if out in succ or inp in occupied:raise AssertionError("reused socket")
        succ[out]=inp;occupied.add(inp)
    def series(parts):
        parts=[p for p in parts if p is not None]
        if not parts:return None
        for p,q in zip(parts,parts[1:]):wire(p[1],q[0])
        return parts[0][0],parts[-1][1]
    def either(parts):
        if len(parts)==1:return parts[0]
        split=gate();merge=gate()
        branches=[parts[0],either(parts[1:])]
        for j,part in enumerate(branches):
            if part is None:wire(split+j,merge+j)
            else:
                wire(split+j,part[0]);wire(part[1],merge+j)
        return split,merge+1
    lanes=[[[],[]] for _ in range(n)];picks=[]
    for clause in clauses:
        choices=[]
        for literal in clause:
            if not 1<=abs(literal)<=n:raise ValueError("invalid literal")
            h=gate()
            # Blocker path uses off, selected clause occurrence uses on.
            lanes[abs(literal)-1][int(literal<0)].append((h,h))
            choices.append((h+1,h+2))
        picks.append(choices)
    stages=[either([series(L) for L in pair]) for pair in lanes]
    stages.extend(either(C) for C in picks)
    s,t=series(stages)
    if s in occupied or t in succ:raise AssertionError("marked socket is internal")
    starts=[x for x in range(3*ng) if x not in occupied]
    sinks=[x for x in range(3*ng) if x not in succ]
    if len(starts)!=len(sinks):raise AssertionError("unbalanced patch")
    return ng,succ,starts,sinks,s,t


def reaches(net,mask):
    ng,succ,starts,sinks,x,t=net
    seen=set()
    while x not in seen:
        seen.add(x)
        g,j=divmod(x,3)
        out=3*g+(j+((mask>>g)&1))%3
        if out not in succ:return out==t
        x=succ[out]
    raise AssertionError('external input entered closed circuit')


def sat(n,clauses):
    return any(all(any(bits[abs(l)-1]==(l>0) for l in c) for c in clauses)
               for bits in product((False,True),repeat=n))


if __name__=='__main__':
    formulas=[(1,[(1,),(-1,)]),(1,[(1,1,1),(-1,-1,-1)]),
              (1,[(1,)]),(1,[(-1,-1,-1)]),
              (2,[(1,2),(-1,2)]),(2,[(1,2),(-1,),(-2,)]),
              (2,[(1,),(-1,2),(2,)]),(3,[(1,-2,3),(-1,)])]
    masks=hits=0
    for n,c in formulas:
        net=compile_open(n,c);g,_,ins,outs,s,t=net
        yes=[m for m in range(1<<g) if reaches(net,m)]
        if bool(yes)!=sat(n,c):raise AssertionError(c)
        occ=sum(map(len,c));forks=n+sum(len(a)-1 for a in c)
        if (g,len(ins))!=(occ+2*forks,1+occ+3*forks):raise AssertionError((g,len(ins)))
        masks+=1<<g;hits+=len(yes)
        print(c,'gates',g,'arity',len(ins),'s,t',s,t,'first mask',min(yes,default=None))
    print(len(formulas),'formulas;',masks,'masks;',hits,'successful routes')
