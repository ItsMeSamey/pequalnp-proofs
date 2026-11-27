"""Source FD preflight followed by a canonical translation-key dictionary."""
from itertools import combinations
from math import comb
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-proxy-native'))
from proxy import recode,accepts_cnf
from prefix import diagram,binary_model
from coset import tail_equations,kernel,orbit_key,from_forbidden,insert

def dependencies(rows):
    grouped={}
    for row in rows:
        scope=tuple(sorted(abs(l) for l in row))
        bad=sum(1<<j for j,v in enumerate(scope) if -v in row)
        grouped[scope]=grouped.get(scope,(1<<(1<<len(scope)))-1)&~(1<<bad)
    rules=[]
    for scope,tab in grouped.items():
        vals=[x for x in range(1<<len(scope)) if tab>>x&1]
        for j,v in enumerate(scope):
            others=[i for i in range(len(scope)) if i!=j]
            for h in range(len(others)+1):
                for sub in combinations(others,h):
                    m=sum(1<<i for i in sub)
                    if all((a&m)!=(b&m) or not ((a^b)>>j&1) for a in vals for b in vals):
                        rules.append((tuple(scope[i] for i in sub),v))
    return rules

def solve_cnf(n,clauses,*,key_bound_cap=1024):
    if key_bound_cap is not None and (type(key_bound_cap) is not int or key_bound_cap<1):
        raise ValueError('invalid key bound cap')
    raw=tuple(tuple(c) for c in clauses);chart=recode(n,raw)
    if chart is None:return dict(status='skip',reason='source width')
    rec,orig,data,masters,copies=chart;N=n+len(copies)
    selectors=tuple(orig[v] for v in masters);index={s:i+1 for i,s in enumerate(selectors)}
    banks=[[[],[]] for i in range(len(selectors)+1)];phys=[[] for _ in banks]
    for row in rec:
        g=[l for l in row if abs(l) in index]
        if len(g)>1:raise AssertionError('multiple guards')
        i=index[abs(g[0])] if g else 0
        banks[i][int(bool(g and g[0]<0))].append(tuple(l for l in row if l not in g))
        phys[i].append(row)
    scopes=[{abs(l) for arm in bank for r in arm for l in r} for bank in banks]
    suffix=[set() for _ in banks]
    for i in reversed(range(len(banks)-1)):suffix[i]=suffix[i+1]|scopes[i+1]
    seen=set();known=set();rules=[];plans=[];candidate_bound=1
    cuts=[];cost=dict(cuts=cuts,binary_probes=0,generated=0,retained=[],copies=copies)
    for i,rows in enumerate(phys):
        rules.extend(dependencies(rows))
        if i:known.add(selectors[i-1])
        while True:
            old=len(known)
            for before,v in rules:
                if all(x in known for x in before):known.add(v)
            if len(known)==old:break
        seen|=scopes[i];front=tuple(sorted(seen&suffix[i]))
        tail=(r for bank in phys[i+1:] for r in bank)
        basis=kernel(N,tail_equations(tail,fixed=selectors[:i]))
        mask=sum(1<<(v-1) for v in front);pivots={}
        for w in basis:insert(pivots,w&mask,0)
        b=len(front);c=sum(v not in known for v in front);d=b-len(pivots)
        bound=0
        for h in range(c+1):
            bound+=comb(b,h) << (d+2*h+4*comb(h,2))
            if key_bound_cap is not None and bound>key_bound_cap:break
        cuts.append(dict(b=b,c=c,d=d,key_bound=bound,bound_complete=h==c))
        if key_bound_cap is not None and bound>key_bound_cap:
            return dict(status='skip',reason='unproven key budget',cost=cost)
        plans.append((front,basis))
        if i+1<len(phys):candidate_bound+=2*bound
    cost['candidate_bound']=candidate_bound
    states=[(frozenset(),0)]
    for i,(front,basis) in enumerate(plans):
        trie={};next_states=[]
        for D,word in states:
            for val,arm in enumerate(banks[i] if i else banks[i][:1]):
                cost['generated']+=1
                E=diagram(N,list(D)+arm,front,cost)
                if E is None:continue
                key,_=orbit_key(from_forbidden(front,E),basis)
                local,phase=key
                code=bytes(table for _,table in local)+phase.to_bytes((2*len(local)+7)//8,'little')
                node=trie
                for byte in code:node=node.setdefault(byte,{})
                if 256 not in node:
                    node[256]=True
                    s=word|((val<<(selectors[i-1]-1)) if i else 0)
                    next_states.append((E,s))
        states=next_states;cost['retained'].append(len(states))
        if len(states)>cuts[i]['key_bound']:raise AssertionError('bound violated')
        if not states:return dict(status='unsat',cost=cost)
    _,word=states[0];selected=list(banks[0][0])
    for i,s in enumerate(selectors,1):selected.extend(banks[i][(word>>(s-1))&1])
    y=binary_model(N,selected)
    if y is None:raise AssertionError('retained prefix lost')
    for s in selectors:y&=~(1<<(s-1))
    y|=word
    if not accepts_cnf(rec,y):raise AssertionError('recoded witness failed')
    x=sum(((y>>(q-1))&1)<<(v-1) for v,q in orig.items())
    if not accepts_cnf(raw,x):raise AssertionError('original witness failed')
    return dict(status='sat',witness=x,cost=cost)
