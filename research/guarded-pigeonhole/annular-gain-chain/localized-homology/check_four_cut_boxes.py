"""Independent contraction, forest lifting, and exact packing comparisons."""
from itertools import combinations_with_replacement, permutations
from random import Random


def cycles(perm):
    labels={}
    for x in perm:
        root=x
        while x not in labels:
            labels[x]=root
            x=perm[x]
    return labels


def analyze(sigma,b,census):
    n=len(sigma);g=n//3;allg=(1<<g)-1
    source={j:i//3 for i,j in enumerate(sigma)}
    shores={}
    for S in range(1,allg):
        incoming=[j for j in range(n) if S>>(j//3)&1 and not S>>source[j]&1]
        if len(incoming)<2:return
        if len(incoming)!=2 or S.bit_count()>b:continue
        internal={j for j in range(n) if S>>(j//3)&1 and S>>source[j]&1}
        shores[S]=(incoming,internal)
    if not shores:return
    census['hosts']+=1
    def step(x,m):
        return sigma[3*(x//3)+(x%3+(m>>(x//3)&1))%3]
    direct=[cycles({x:step(x,m) for x in range(n)}) for m in range(1<<g)]
    cached={}
    def table(S):
        if S not in cached:
            incoming,_=shores[S];choices={}
            m=S
            while True:
                destinations=[]
                for x in incoming:
                    while S>>(x//3)&1:x=step(x,m)
                    destinations.append(x)
                choices[tuple(destinations)]=m
                if not m:break
                m=(m-1)&S
            cached[S]=list(choices.items())
        return cached[S]
    for a,d in combinations_with_replacement(range(n),2):
        eligible=[S for S,(_,internal) in shores.items() if a not in internal and d not in internal]
        packs={0}
        for S in eligible:packs|={u|S for u in packs if not u&S}
        opt=max(u.bit_count() for u in packs)
        census['pack_checks']+=1
        # All maximal-greedy tie choices, including overlapping incomparable cuts.
        def greedy(used):
            choices=[S for S in eligible if not S&used]
            if not choices:return [()]
            result=[]
            for S in choices:
                if not any(S!=z and S&z==S for z in choices):
                    result.extend((S,*rest) for rest in greedy(used|S))
            return result
        choices=set(tuple(sorted(p)) for p in greedy(0))
        if any(sum(S.bit_count() for S in packing)!=opt for packing in choices):
            raise AssertionError(('packing',sigma,a,d))
        packing=min(choices)
        residual=allg^sum(packing)
        live=set(range(n)).difference(*(shores[S][1] for S in packing))
        expected=any(L[a]==L[d] for L in direct)
        found=False;m=residual
        while True:
            perm={x:step(x,m) for x in live if residual>>(x//3)&1}
            flex=[];mask=m
            for S in packing:
                ins=shores[S][0];options=table(S)
                outputs,base=options[0]
                perm.update(zip(ins,outputs));mask|=base
                if len(options)==2:flex.append((ins,base^options[1][1]))
            L=cycles(perm)
            parent={v:v for v in L.values()}
            def find(x):
                while x!=parent[x]:x=parent[x]
                return x
            for (i,j),flip in flex:
                u,v=find(L[i]),find(L[j])
                if u!=v:
                    parent[u]=v;mask^=flip
            match=find(L[a])==find(L[d])
            if match!=(direct[mask][a]==direct[mask][d]):
                raise AssertionError(('lift',sigma,a,d,mask))
            refinements=[L0 for t,L0 in enumerate(direct) if t&residual==m]
            if match!=any(L0[a]==L0[d] for L0 in refinements):
                raise AssertionError(('branch',sigma,a,d,m))
            found|=match;census['branches']+=1
            if not m:break
            m=(m-1)&residual
        if found!=expected:raise AssertionError(('decision',sigma,a,d))
        census['yes' if found else 'no']+=1


if __name__=='__main__':
    totals=dict.fromkeys(('hosts','pack_checks','branches','yes','no'),0)
    for p in permutations(range(6)):analyze(p,1,totals)
    rng=Random(24701)
    for g in (3,4,5):
        for trial in range(45):
            analyze(rng.sample(range(3*g),3*g),1+trial%(g-1),totals)
    print(totals)
