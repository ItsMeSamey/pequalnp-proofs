"""Stage 2 automatic tree and physical macro/raw comparison."""
import json
from itertools import combinations
from math import prod
import event_auto
import event_csp
import event_macro
import event_decompose
import event_tree
from check_event_tree_native import source_words
from event_fixtures import crossing_ladder, nested_skew
from stage2_event_fixtures import saved_top

def lift(chart,words):
    names={u:(('site',17*i) if i%2 else frozenset([i])) for i,u in enumerate(chart.domains)}
    ds={names[u]:chart.domains[u] for u in reversed(chart.domains)}
    cs=[(names[u],names[v],r) for u,v,r in reversed(chart.constraints)]
    tree=event_decompose.decompose(ds,[(u,v) for u,v,_ in cs])
    assert tree['status']=='ok'
    r=event_tree.solve(ds,cs,tree['bags'],tree['tree_edges'],names[chart.output])
    assert set(r['witnesses'])=={v[-1] for v in words.values()}
    assert r['states']==sum(prod(len(ds[u]) for u in bag) for bag in tree['bags'])
    for bit,w in r['witnesses'].items():
        s=chart.replay({u:w[t] for u,t in names.items()})
        assert words[s['physical']]==(s['key'],s['underlying'],bit)

def run(label,f,rename=False):
    args=tuple(f[k] for k in ('challenge','n','aliases','table','initial','bottom','outputs'))
    occ,ids=(f[k] for k in ('occurrence_pins','id_pins'))
    words,_=source_words(*args[:3],args[3:],occ,ids)
    if label=='restore':
        assert {x[0]:x[-1] for x in words.values()}=={45:1,47:0}
    bits={v[-1] for v in words.values()}
    metrics={}
    for backend in ('raw','macro'):
        schedule=f['schedule'] if backend=='raw' else f.get('macro_schedule')
        r=event_auto.solve(*args,backend=backend,occurrence_pins=occ,id_pins=ids,schedule=schedule)
        assert r['status']==('empty','constant','pair')[len(bits)],(label,backend,r.get('reason'))
        assert {s['prediction'] for s in r['samples']}==bits
        for s in r['samples']:
            assert words[s['physical']]==(s['key'],s['underlying'],s['prediction'])
        m=r['metrics']
        assert m['backend']==backend and m['steps']>=m['states']==m['bag_row_bound']>0
        assert m['decomposition_attempts']>=1 and m['width']<=3
        assert m['replay_bytes']==sum(len(s['physical']) for s in r['samples'])
        assert m['domain_records']>=m['domain_records_post'] and m['candidate_pairs']>=m['retained_pairs']
        metrics[backend]=m
        if rename:
            chart=(event_csp if backend=='raw' else event_macro).build(*args,schedule=schedule)
            lift(chart,words)
    assert metrics['macro']['vertices']<metrics['raw']['vertices']
    print(label,json.dumps(metrics,sort_keys=True,default=str))

def main():
    names=[3,'A',('x',),frozenset([0]),('y',)]
    for n,expected in ((4,'ok'),(5,'unknown')):
        t=event_decompose.decompose(names[:n],combinations(names[:n],2))
        assert t['status']==expected
        if n==4:
            assert t['width']==3 and t['apex'] in names[:4]
        else:
            assert t['attempts']==n+1
    crossed=crossing_ladder(3)
    crossed['aliases']=[-41,7,-990,-41,7,-990,13]
    run('crossed',crossed,True)
    run('nested',nested_skew(2,mismatch=True))
    run('restore',saved_top())
    print('physical macro/raw, opaque relabelled lifts and complete counters passed')
if __name__=='__main__':
    main()
