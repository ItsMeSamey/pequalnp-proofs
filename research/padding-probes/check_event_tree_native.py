from padding_cnf import encode
from event_tree import solve

def run_machine(M,raw):
    T,q,bottom,out=M;stack=[bottom];height=0
    for byte in raw:
        q,act,*args=T[q,stack[-1],byte]
        if act=='push':stack.append(args[0]);height=max(height,len(stack)-1)
        elif act=='pop':assert len(stack)>1;stack.pop()
        else:assert act=='stay'
    return int(out[q]),height

def raw_key(raw,n):
    lines=raw.splitlines();nv,nc=map(int,lines[0].split()[2:])
    rows=[tuple(map(int,line.split()[:-1])) for line in lines[1:]]
    assert nc==len(rows) and nv==4*n+6
    core=rows[-(n+9):-(n+1)]
    for value in range(8):
        word=value<<n
        assert any(all(bool((word>>(abs(l)-1))&1)!=(l>0) for l in row) for row in core)
    return sum((row[0]<0)<<i for i,row in enumerate(rows[-(n+1):]))

def normalize(a):
    return (abs(a),int(a<0)) if isinstance(a,int) else a

def source_words(ch,n,aliases,M,occ,idp):
    expected={};h=0
    for k in range(1<<(n+1)):
        ids={};ok=True
        for i,a in enumerate(aliases):
            v,offset=normalize(a);b=((k>>i)&1)^offset
            if ids.setdefault(v,b)!=b:ok=False
        if not ok or any((k>>i)&1!=v for i,v in occ) or any(ids[i]!=v for i,v in idp):continue
        raw=encode(ch,n,k);assert raw_key(raw,n)==k
        y,z=run_machine(M,raw);h=max(h,z);expected[raw]=(k,ids,y)
    return expected,h

def malformed():
    ds={0:(0,1),1:(0,1)};cs=[(0,1,{(0,0),(1,1)})]
    for bags,edges in (([(0,1),(1,),(0,)],[(0,1),(1,2)]), ([(0,),(1,)],[(0,1)]),
                       ([(0,1),(0,1)],[]), ([(0,0,1)],[]), ([(0,)],[])):
        try:solve(ds,cs,bags,edges,0)
        except ValueError:pass
        else:raise AssertionError('malformed supplied decomposition')
    assert solve(ds,cs+[(0,0,set())],[(0,1)],[],0)['status']=='empty'

def cases(name,f,extra_occ=(),extra_id=(),caps=False):
    from event_csp import build
    ch,n,aliases=(f[x] for x in ('challenge','n','aliases'))
    M=tuple(f[x] for x in ('table','initial','bottom','outputs'))
    c=build(ch,n,aliases,*M,schedule=f['schedule'])
    p=lambda v:list(v.items()) if hasattr(v,'items') else list(v)
    occ=p(f['occurrence_pins'])+list(extra_occ);idp=p(f['id_pins'])+list(extra_id)
    expected,height=source_words(ch,n,aliases,M,occ,idp);bits={value[-1] for value in expected.values()}
    domains=dict(c.domains)
    # Put each ID pin at ONE real marker; links must propagate it to all other copies.
    for var,b in idp:
        a=next(i for i,x in enumerate(aliases) if normalize(x)[0]==var)
        occ.append((a,b^normalize(aliases[a])[1]))
    for i,b in occ:
        site=c.slot_events[i];domains[site]=[v for v in domains[site] if v.bit==b]
    args=(domains,c.constraints,f['bags'],f['tree_edges'],c.output)
    r=solve(*args)
    assert set(r['witnesses'])==bits and r['status']==('empty','constant','pair')[len(bits)],(name,r)
    for y,w in r['witnesses'].items():
        orig=c.replay(w);k,ids,value=expected[orig['physical']]
        assert (orig['key'],orig['prediction'],y)==(k,value,value)
    if caps:
        for limits in ({'state_cap':0},{'step_cap':0}):
            v=solve(*args,**limits);assert v['status']=='unknown' and not v['witnesses']
    print(name,len(expected),sorted(bits),height,r['width'],r['states'],r['steps'])
    return height

def elim(c):
    g={v:set() for v in c.domains}
    for u,v,_ in c.constraints:
        if u!=v:g[u].add(v);g[v].add(u)
    seq=[];bags=[]
    while g:
        u=min(g,key=lambda v:(len(g[v]),repr(v)))
        S=g.pop(u);seq.append(u);bags.append((u,*S))
        for v in S:g[v].remove(u);g[v].update(S-{v})
    pos={u:i for i,u in enumerate(seq)}
    return bags,[(i,min((pos[v] for v in bag[1:]),default=len(bags)-1)) for i,bag in enumerate(bags[:-1])]

def restore():
    from event_csp import build
    from stack_align_padding import _comparator
    M=_comparator([],['push','push','pop','pop','gate']);aliases=[1,2,3,4,5]
    c=build([],4,aliases,*M)
    bags,tree_edges=elim(c)
    f=dict(challenge=[],n=4,aliases=aliases,schedule=None,table=M[0],initial=M[1],bottom=M[2],
           outputs=M[3],bags=bags,tree_edges=tree_edges,occurrence_pins=[],id_pins=[])
    assert cases('two pushes, distinct saved tops',f)==2

if __name__=='__main__':
    from event_fixtures import crossing_ladder,nested_skew,state_dependent
    from event_csp import ScheduleMismatch,build
    malformed()
    f=crossing_ladder(2)
    cases('crossed switches',f,caps=True)
    cases('physical enable unit',f,extra_occ=[(4,0)])
    del f
    f=crossing_ladder(2,mismatch=True)
    cases('signed crossing and alias pin',f,extra_id=[(1,1)])
    cases('conflicting signed pins',f,extra_occ=[(0,1),(2,1)])
    del f
    cases('nested signed',nested_skew(1,mismatch=True))
    restore()
    f=state_dependent();M=tuple(f[z] for z in ('table','initial','bottom','outputs'))
    assert [run_machine(M,encode([],2,k))[0] for k in (4,5)]==[0,1]
    for sched in (None,f['schedule']):
        try:build([],2,f['aliases'],*M,schedule=sched)
        except ScheduleMismatch:pass
        else:raise AssertionError('data-dependent schedule accepted')
    print('invalid tree, empty, caps and two data-dependent refusals passed')

def public_controls():
    from event_solver import solve as public
    from event_fixtures import crossing_ladder,state_dependent
    def call(f,occ=(),idp=(),invalid=False,**kw):
        ch,n,aliases=(f[x] for x in ('challenge','n','aliases'))
        M=tuple(f[x] for x in ('table','initial','bottom','outputs'))
        out=public(ch,n,aliases,*M,([] if invalid else f['bags']),([] if invalid else f['tree_edges']),
                   schedule=f['schedule'],occurrence_pins=occ,id_pins=idp,**kw)
        exp,_=source_words(ch,n,aliases,M,occ,idp)
        for sample in out['samples']:
            assert (sample['key'],sample['underlying'],sample['prediction'])==exp[sample['physical']]
        return out,{z[-1] for z in exp.values()}
    for mismatch in (False,True):
        f=crossing_ladder(2,mismatch=mismatch)
        r,bits=call(f,occ=[(1,0)],idp=[(1,1)])
        assert {s['prediction'] for s in r['samples']}==bits
        assert r['status']==('empty','constant','pair')[len(bits)]
        print('public signed/pinned',mismatch,r['status'],len(r['samples']))
    assert call(f,occ=[(0,1),(2,1)])[0]['status']=='empty'
    assert call(f,state_cap=0)[0]['status']=='unknown'
    assert call(f,invalid=True)[0]['status']=='unknown'
    del f
    assert call(state_dependent())[0]['status']=='unknown'
    print('public contradictory pins, invalid tree, schedule refusal, and cap passed')

if __name__=='__main__':public_controls()
