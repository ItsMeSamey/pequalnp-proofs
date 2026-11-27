"""Tiny comparisons with expression trees evaluated on the original primary inputs."""
from collections import Counter
from random import Random

def encode(n,tree):
    gates=[]
    def visit(node):
        if isinstance(node,int):return 1<<(node+1)
        op,*args=node
        if op=='lit':return args[0]
        a=visit(args[0])
        if op=='not':return a^1
        b=visit(args[1])
        if op=='xor':return a^b
        gates.append((a,b))
        return 1<<(n+len(gates))
    y=visit(tree)
    return tuple(gates),y

def evaluate(node,word):
    if isinstance(node,int):return (word>>node)&1
    op,*args=node
    if op=='lit':return args[0]
    a=evaluate(args[0],word)
    if op=='not':return 1-a
    b=evaluate(args[1],word)
    return (a^b) if op=='xor' else (a*b)

def examples():
    rng=Random(90277)
    out=[(0,('lit',0)),(0,('lit',1)),(1,('and',0,('not',0)))]
    for n in range(1,5):
        nodes=list(range(n))
        for _ in range(9):
            a,b=rng.choices(nodes,k=2)
            t=(rng.choice(('and','xor')),a,b)
            if rng.randrange(2):t=('not',t)
            nodes.append(t);out.append((n,t))
        shared=('and',nodes[-1],nodes[-3])
        out.append((n,('and',shared,('not',shared))))
    term=('and',0,1)
    padded=term
    for _ in range(11):padded=('and',padded,term)
    out.extend([(2,padded),(2,('and',padded,('not',term)))])
    return out

def audit(solver, name, budgets):
    stats=Counter()
    for n,tree in examples():
        gates,y=encode(n,tree)
        models={u for u in range(1<<n) if evaluate(tree,u)}
        for budget in budgets:
            result=solver(n,gates,y,budget=budget)
            status=result['status']
            stats[budget,status]+=1
            if status=='skip':continue
            if status!=('sat' if models else 'unsat'):raise AssertionError((name,tree,result))
            if 'count' in result and result['count']!=len(models):raise AssertionError((name,'count',tree,result))
            if models and result.get('witness') not in models:raise AssertionError((name,'physical',tree,result))
    return sorted(stats.items())

if __name__=='__main__':
    import affine_quotient,backward_bank,reachable_span
    for mod in (affine_quotient,backward_bank,reachable_span):
        print(mod.__name__,audit(mod.solve,mod.__name__,[1,2000]))

def integrated():
    import portfolio
    from original_cnf import compile_cnf
    rng=Random(146)
    inputs=[]
    for n,tree in examples():
        gates,y=encode(n,tree)
        inputs.append((n,gates,y,{x for x in range(1<<n) if evaluate(tree,x)}))
    controls=[(2,[(1,2),(1,-2),(-1,2),(-1,-2)]),(0,[()]),(0,[]),(3,[(1,-1),(2,2)])]
    for z in range(30):
        n=1+z%4
        controls.append((n,[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))) for _ in range(rng.randrange(1,7))]))
    for n,clauses in controls:
        gs,y=compile_cnf(n,clauses)
        good={x for x in range(1<<n) if all(any(x//2**(abs(l)-1)%2==int(l>0) for l in c) for c in clauses)}
        inputs.append((n,gs,y,good))
    for n,m in ((2,9),(3,4),(4,7)):
        for _ in range(14):
            gs=[];dense=[]
            for j in range(m):
                pair=[rng.sample(range(1+n+j),rng.randrange(1,2+n+j)) for k in range(2)]
                gs.append(tuple(sum(1<<i for i in row) for row in pair));dense.append(pair)
            oi=rng.sample(range(1+n+m),rng.randrange(1,2+n+m))
            out=sum(1<<i for i in oi)
            good=set()
            for x in range(1<<n):
                signals=[1]+[x//2**i%2 for i in range(n)]
                for l,r in dense:
                    signals.append((sum(signals[i] for i in l)%2)*(sum(signals[i] for i in r)%2))
                if sum(signals[i] for i in oi)%2:good.add(x)
            inputs.append((n,gs,out,good))
    tally=Counter()
    for n,gs,out,good in inputs:
        for label,routes,budget,rw in (('default',None,2000,8),('zero',None,0,0),('empty',[],2000,0),
                *((name,[name],2000,0) for name in portfolio.ROUTES)):
            r=portfolio.solve(n,gs,out,routes=routes,budget=budget,rewrite_budget=rw)
            w=r['witness'];c=r['cost']
            if r['status']!=('sat' if good else 'unsat') or (good and w not in good):raise AssertionError((label,n,gs,out,r))
            if c['raw_n']!=n or c['raw_ands']!=len(gs) or c['fallback_evaluations']>1<<n:raise AssertionError(c)
            if (r['route']=='exhaustive' and not good and c['fallback_evaluations']!=1<<n) or c['replay_evaluations']!=int(bool(good)):raise AssertionError(c)
            tally[label,r['route'],r['status']]+=1
    print('integrated',len(inputs),'cases',sum(tally.values()),'calls')
    for key in sorted(tally):print(*key,tally[key])

if __name__=='__main__':
    import grouped_mask
    print('grouped_mask',audit(grouped_mask.solve,'grouped_mask',[1,2000]))
    integrated()

def fault_controls():
    from unittest.mock import patch
    import portfolio,affine_quotient
    args=(2,[(2,4)],8)
    def run(answer):
        with patch.object(affine_quotient,'estimate',return_value=1),patch.object(affine_quotient,'solve',return_value=answer):
            return portfolio.solve(*args,routes=['affine_quotient'],budget=10,rewrite_budget=0)
    for status in ('skip','unknown','timeout'):
        r=run({'status':status})
        assert (r['route'],r['witness'])==('exhaustive',3)
        assert r['cost']['attempts'][0]['status']==status
    for phase in ('estimate','solve'):
        with patch.object(affine_quotient,'estimate',return_value=1),patch.object(affine_quotient,phase,side_effect=TimeoutError):
            r=portfolio.solve(*args,routes=['affine_quotient'],budget=10,rewrite_budget=0)
            assert (r['route'],r['witness'])==('exhaustive',3)
            assert r['cost']['attempts'][0]['status']==('estimate_timeout' if phase=='estimate' else 'timeout')
    large=portfolio.solve(15000,[],1<<15000,budget=0)
    assert large['witness']==1<<14999 and large['cost']['raw_n']==15000
    for bad in ({'status':'sat','witness':0},{'status':'sat','witness':4},{'status':'sat'},{'status':'nonsense'}):
        try:run(bad)
        except RuntimeError:pass
        else:raise AssertionError(bad)
    # A deliberately lying UNSAT backend is trusted: documents a verifier boundary.
    assert run({'status':'unsat'})['status']=='unsat'
    a=portfolio.solve(*args);b=portfolio.solve(*args)
    assert (a['route'],a['witness'])==(b['route'],b['witness'])
    print('fault controls: skip/unknown/timeouts fall back; 15000-bit affine witness passes; four malformed/corrupt results reject; backend UNSAT trusted; repeat selection matches')

if __name__=='__main__':fault_controls()
