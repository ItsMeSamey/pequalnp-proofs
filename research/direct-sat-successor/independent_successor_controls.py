"""Verify the successor against independent primary-input truth tables on tiny circuits."""
from collections import Counter
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'direct-sat-portfolio'))
from independent_controls import examples,encode,evaluate
from original_cnf import compile_cnf

def cases():
    for n,t in examples():
        g,o=encode(n,t)
        yield n,g,o,{w for w in range(1<<n) if evaluate(t,w)}
    forms=[[(1,2),(1,-2),(-1,2),(-1,-2)],[(1,2),(-1,2),(1,-2)],[(1,),(-1,)],[(1,-1)],[]]
    for f in forms:
        g,o=compile_cnf(2,f)
        yield 2,g,o,{w for w in range(4) if all(any(((w>>(abs(l)-1))&1)==int(l>0) for l in c) for c in f)}
    # Address bit selects the same lane on both banks, followed by one AND.
    n=5
    gs=[(2,4^8),(2,16^32),(4^(1<<6),16^(1<<7))]
    good={x for x in range(32) if x & (1<<(1+(x&1))) and x & (1<<(3+(x&1)))}
    yield n,gs,1<<8,good

def run():
    import successor
    from unittest.mock import patch
    counts=Counter();statuses=Counter()
    configs=[
        ('default',{}),
        ('reverse',dict(schedule=('raw','normalized'))),
        ('normalized',dict(schedule=('normalized',))),
        ('raw_reversed_bits',dict(schedule=('raw',))),
        ('tiny',dict(automata_budget=1,rank_cap=1,prefix_budget=0,budget=0,rewrite_budget=0)),
        ('fallback',dict(schedule=(),prefix_budget=0,routes=[],rewrite_budget=0)),
    ]
    nc=0
    for n,gs,y,good in cases():
        nc+=1
        for tag,opts in configs:
            opts=dict(opts)
            if tag=='raw_reversed_bits':opts['order']=tuple(reversed(range(n)))
            a=successor.solve(n,gs,y,**opts)
            if a['status']!=('sat' if good else 'unsat') or (good and a['witness'] not in good):raise AssertionError((tag,n,gs,y,a))
            c=a['cost']
            assert c['raw_n']==n and c['original_ands']==len(gs)
            assert c['original_replay_evaluations']==bool(good)
            if a['route']=='portfolio/exhaustive':
                e=c['portfolio']['fallback_evaluations']
                assert e<=1<<n and (good or e==1<<n)
            counts[tag,a['route'],a['status']]+=1
            for rec in c['attempts']:statuses[tag,rec['status']]+=1
    print('cases',nc,'decisions',sum(counts.values()))
    print('routes',sorted(counts.items()))
    print('attempts',sorted(statuses.items()))
    args=(2,[(2,4)],8)
    for injected in ('unknown','skip','timeout','thrown','bad','wrong'):
        kwargs={'side_effect':TimeoutError} if injected=='thrown' else {'return_value':{'status':'sat','witness':0} if injected=='wrong' else {'status':injected}}
        with patch.object(successor.implicit_wire_circuit,'solve',**kwargs) as mocked:
            try:r=successor.solve(*args,schedule=('raw','normalized'),prefix_budget=0,routes=[],rewrite_budget=0)
            except RuntimeError:
                if injected not in ('bad','wrong'):raise
            else:
                assert injected not in ('bad','wrong') and r['route']=='portfolio/exhaustive' and r['witness']==3
                state='timeout' if injected=='thrown' else injected
                assert [a['status'] for a in r['cost']['attempts']]==[state,'same_presentation']
            assert mocked.call_count==1
    print('faults: unknown/skip/timeout/thrown fall through once; bad status/wrong witness raise')

if __name__=='__main__':run()

def scarcity():
    import successor
    corpus=list(cases())
    for idx,cap,expect in ((2,10,'affine'),(39,250,'sat'),(45,250,'unsat')):
        n,g,o,good=corpus[idx]
        r=successor.solve(n,g,o,schedule=('raw','normalized'),automata_budget=cap,budget=0,rewrite_budget=0)
        assert [a['status'] for a in r['cost']['attempts']]==['skip',expect]
        assert (r['witness'] in good) if good else (r['status']=='unsat')
        print('scarce original',idx,'raw_n',n,'original_ands',len(g),'budget',cap,'raw skips, normalized',expect)

if __name__=='__main__':scarcity()
