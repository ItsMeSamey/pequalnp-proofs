import argparse,collections,itertools,json,sys,time,hashlib,gzip
from pathlib import Path
D=Path('/workspace/scratch/site-team-04');sys.path.insert(0,str(D/'digest'))
from split179 import emit,evalnet
out=dest=Path('/dev/shm/team04-relaxed170')
archive=Path('/dev/shm/04-merged-terms/joint181-pool-plus-near180.json.gz')
d=json.load(gzip.open(archive));truth=[int(x,16) for x in d['truth']];goal=truth[d['target']];F=(1<<1024)-1
p=argparse.ArgumentParser();p.add_argument('--prefix',nargs=3,metavar=('OP','PORT1','PORT2'));p.add_argument('--cap',type=int,default=170);p.add_argument('--solve',action='store_true');p.add_argument('--seconds',type=float,default=2.5);cli=p.parse_args()
exactmeta=d['controls'][1]
assert exactmeta['sha256'].startswith('45de0355')
def read(path):
    c=json.loads(Path(path).read_bytes());return c.get('net',c)
near=read('/workspace/scratch/site-team-09/cross181-wire104-pin35-180.json');exact=read(exactmeta['file'])
# Physical structural interning, restricted to the two output-plus-marker live cones.
internal={};ordered=[]
def intern(op,ins):
    k=(op,tuple(sorted(ins)))
    if k not in internal:internal[k]=64+len(ordered);ordered.append(k)
    return internal[k]
def cone(c):
    w,mk=evalnet(c['gates']);memo={i:i for i in range(64)}
    def go(i):
        if i not in memo:
            g=c['gates'][i-64];memo[i]=intern(g['op'],[go(a) for a in g['inputs']])
        return memo[i]
    m=go(mk);go(c['output']);return set(memo.values())-set(range(64)),m
ca,ma=cone(near);cb,mb=cone(exact);assert ma==mb
common=ca&cb;remap={i:i for i in range(64)};fixed=[]
# Canonical old structural wire labels are local to ordered; translate to pool truth IDs.
allvals,_=evalnet([dict(op=op,inputs=list(aa)) for op,aa in ordered])
poolid={v:i for i,v in enumerate(truth)}
anc={i:set() for i in range(64)}
for n,(op,aa) in enumerate(ordered,64):anc[n]={n}.union(*(anc[a] for a in aa))
anchor=anc[ma]
baseplan={z:(op,tuple(sorted(ids))) for z,op,*ids in exactmeta['warm_plan']}
alt=collections.defaultdict(set)
for c in d['controls']:
    plan={z:(op,tuple(sorted(ids))) for z,op,*ids in c['warm_plan']}
    for z,expr in plan.items():
        if z in baseplan and expr!=baseplan[z]:alt[z].add((c['sha256'],expr))
# Free a producer's ancestors and every downstream fixed gate consuming a released
# value. The complement remains closed under physical dependencies.
def release(n):
    initial=anc[n]&common-anchor
    return {q for q in common if anc[q]&initial}
cand=[]
for n in sorted(common-anchor):
    z=poolid[allvals[n]]
    if z in alt:
        dead=release(n)
        if not dead&anchor:
            cand.append((n,z,dead))
release_data=[]
for n,z,dropped in cand:
    release_data.append((z,len(anc[n]&common-anchor),len(dropped),len(alt[z])))
print('cuts',release_data,flush=True)
chosen_ids=(285,290,257,206)
selected=[(n,z,drop) for n,z,drop in cand if z in chosen_ids]
assert len(selected)==len(chosen_ids)
released=set.union(*(drop for n,z,drop in selected))
assert not (released&anchor)
release_receipt=dict(original_fixed=len(common),released=len(released),cuts=[
    dict(pool_id=z,alternative_recipes=sorted({expr for _,expr in alt[z]}),baseline_recipe=baseplan[z],
         source_sha256=sorted({h for h,_ in alt[z]}),ancestor_count=len(anc[n]&common-anchor),unfixed_if_alone=len(drop))
    for n,z,drop in selected],released_pool_ids=sorted(poolid[allvals[n]] for n in released))
common-=released
assert all(anc[n]<=common for n in common)
(dest/'cuts.json').write_text(json.dumps(release_receipt))

for n in sorted(common):
    op,ins=ordered[n-64];pins=[remap[a] for a in ins];remap[n]=64+len(fixed);fixed.append(dict(op=op,inputs=pins))
fv,marker=evalnet(fixed);assert remap[ma]==marker
m=dict(fixed_gates=fixed,marker=marker,target=hex(goal));P={v:i for i,v in enumerate(fv)};L=len(fv)
def gate(op,a,b):return a&b if op=='and' else a|b if op=='or' else F^a
recipes=collections.defaultdict(set)
def rec(op,a,b):
    z=gate(op,a,b)
    if z not in P and z not in (a,b):recipes[z].add((op,tuple(sorted((a,b))) if op!='not' else (a,)))
    return z
for z,op,*ids in d['recipes']:
    assert rec(op,truth[ids[0]],truth[ids[-1]])==truth[z]
vocab=set(truth)
def addprefix(op,a,b):
    if op not in ('and','or','not') or a not in P or b not in P:raise ValueError('prefix must use fixed inputs')
    v=gate(op,a,b)
    if v in vocab:return None
    use=set()
    for x in truth:
        for o,z in [('and',x&v),('or',x|v)]:
            if z in vocab and z not in P and z not in (x,v):use.add((o,x,z))
    if F^v in vocab and F^v not in P:use.add(('not',v,F^v))
    return v,use
if cli.prefix:
    op,ai,bi=cli.prefix;a,b=fv[int(ai)],fv[int(bi)];chosen=addprefix(op,a,b)
    if chosen is None:raise ValueError('prefix already in overlay')
else:
    trials=[]
    # Deterministic shortlist of row-25 interactions; explicit --prefix accepts any paid inputs.
    for j,b in enumerate(fv):
        for op in ('and','or'):
            g=addprefix(op,truth[25],b)
            if g:
                new,uses=g;trials.append((len({z for _,_,z in uses}),len(uses),j,op,new,uses))
    _,_,j,op,new,uses=max(trials,key=lambda t:t[:4]);a,b=truth[25],fv[j];chosen=new,uses
v,uses=chosen;assert rec(op,a,b)==v
for o,x,z in uses:assert rec(o,v,x)==z
prefix=dict(op=op,pins=[P[a],P[b]],uses=len(uses),distinct_outputs=len({z for _,_,z in uses}),truth=hex(v))
def decode(plan):
    nodes=P.copy();active=[];gs=[]
    def go(z):
        if z in nodes:return nodes[z]
        if z in active:raise ValueError(active[active.index(z):])
        active.append(z);op,ins=plan[z];pins=[go(a) for a in ins];active.pop();nodes[z]=L+len(gs);gs.append(dict(op=op,inputs=pins));return nodes[z]
    y=go(goal);return dict(gates=gs,output=y)
plans=[]
for ci in (1,0,18):
    plan={truth[z]:(op,tuple(sorted(truth[k] for k in ids))) for z,op,*ids in d['controls'][ci]['warm_plan']}
    tail=decode(plan);full,report=emit(m,tail)
    assert not report['false_negatives'] and not report['false_positives'] and report['shard']==53
    plans.append(plan);(dest/f'warm-{ci}-{report["size"]}.json').write_text(json.dumps(full))
    print('control',ci,report,flush=True)
assert len(fixed)+len(decode(plans[0])['gates'])==181
print('fixed gates',len(fixed),'charged near output',328,'one prefix',prefix['pins'],prefix['op'],'new exits',prefix['uses'],flush=True)
nearplan={truth[z]:(o,tuple(sorted(truth[i] for i in ids))) for z,o,*ids in d['approximate_controls'][0]['warm_plan']}
repair=dict(nearplan);repair.update(plans[0]);repair[truth[137]]=('or',tuple(sorted([truth[25],truth[325]])))
rt=decode(repair);net,report=emit(m,rt);assert report['size']==181 and report['false_negatives']==report['false_positives']==0
assert truth[325] in evalnet(net['gates'])[0][L:]
(dest/'near-repair-warm.json').write_text(json.dumps(net));plans.append(repair)
orig={z for z in recipes if z!=v};added={v}
seen=set();stack=[goal]
while stack:
    z=stack.pop()
    if z in seen or z in P:continue
    seen.add(z)
    for op,ins in recipes[z]:stack.extend(ins)
assert truth[328] in seen and truth[328] not in P
N={z:i+1 for i,z in enumerate(sorted(seen))};counter=len(N);cl=[[N[goal]]];sel={};owners={};users=collections.defaultdict(list);atmost=[]
for z,n in N.items():
    opts=[]
    for op,ins in sorted(recipes[z]):
        counter+=1;t=counter;sel[t]=(z,op,ins);owners[z,op,ins]=t;opts.append(t)
        cl.append([-t,n])
        for a in set(ins)-P.keys():
            cl.append([-t,N[a]]);users[a].append(t)
    cl.append([-n,*opts])
    if len(opts)>1:atmost.append(opts)
for z,n in N.items():
    if z!=goal:cl.append([-n,*users[z]])
phase=[]
for plan in plans:
    cone=set();stk=[goal];lits=set()
    while stk:
        z=stk.pop()
        if z in P or z in cone:continue
        cone.add(z);op,ins=plan[z];lits.update((N[z],owners[z,op,ins]));stk.extend(ins)
    assert all(any((abs(i) in lits)==(i>0) for i in row) for row in cl)
    phase.append(lits)
receipt=dict(values=len(N),original=len(orig),new_reachable=len(added&seen),recipes=len(sel),clauses=len(cl),warm_tails=[sum(n in s for n in N.values()) for s in phase])
(dest/'stage.json').write_text(json.dumps(receipt));print(receipt,flush=True)
#unused=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=181-len(m['fixed_gates'])-1);p.add_argument('--solve',action='store_true');p.add_argument('--seconds',type=float,default=2.5);args=p.parse_args()
args=cli;args.cap-=len(fixed)
receipt.update(fixed=len(fixed),variable_budget=args.cap,prefix=prefix,near_variable=N[truth[328]],archive_sha=hashlib.sha256(archive.read_bytes()).hexdigest())
(dest/'stage.json').write_text(json.dumps(receipt))
if not args.solve:sys.exit()
from pysat.solvers import Minicard
with Minicard(bootstrap_with=cl) as solver:
    for opts in atmost:solver.add_atmost(opts,1)
    solver.add_atmost(list(N.values()),args.cap)
    warm=min(reversed(phase),key=len)
    solver.set_phases([j if j in warm else -j for j in range(1,counter+1)])
    deadline=time.process_time()+args.seconds;cuts=0
    while time.process_time()<deadline:
        solver.conf_budget(200);ans=solver.solve_limited()
        if ans is None:continue
        if not ans:print('UNSAT restricted family');break
        pos=set(solver.get_model());chosen={z:(op,ins) for t,(z,op,ins) in sel.items() if t in pos}
        try:tail=decode(chosen)
        except ValueError as err:
            solver.add_clause([-owners[z,*chosen[z]] for z in err.args[0]]);cuts+=1;continue
        # A disconnected active component satisfying consumer clauses must contain a cycle.
        done=set();active=[]
        def inspect(z):
            if z in P or z in done:return
            if z in active:raise ValueError(active[active.index(z):])
            active.append(z)
            for a in chosen[z][1]:inspect(a)
            active.pop();done.add(z)
        try:
            for z in chosen:inspect(z)
        except ValueError as err:
            solver.add_clause([-owners[z,*chosen[z]] for z in err.args[0]]);cuts+=1;continue
        assert len(tail['gates'])==len(chosen)
        net,report=emit(m,tail)
        assert report['suffix_count']<=args.cap and report['shard']==53 and report['false_positives']==report['false_negatives']==0
        (dest/f"full-{report['size']}.json").write_text(json.dumps(net));print('SAT',report);break
    else:print('UNKNOWN',solver.accum_stats(),'cycle_cuts',cuts)
