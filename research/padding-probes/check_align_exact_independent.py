"""Exhaustive physical reference for the small signed/pinned recognition fixture."""
from itertools import product
from padding_cnf import encode
from stack_align_exact import probe
from stack_align_pins import compile_pins, complete_prefix

ALIASES=(1,2,3,-2,4)
N=len(ALIASES)-1
CS=[(1,-2,3)]
RAW={k:encode(CS,N,k) for k in range(1<<len(ALIASES))}
FIRST=1+len(CS)+8

def legal(k,occ,ids):
    bits=[(k>>i)&1 for i in range(len(ALIASES))]
    if bits[1]==bits[3]:
        return False
    return all(bits[i]==v for i,v in occ) and all(bits[(1,2,3,4).index(i) if i!=4 else 4]==v for i,v in ids)

def machine(mode):
    # Key signs appear on first byte of each marker line.
    end=FIRST+len(ALIASES)
    states=list(product(range(end+1),(False,True),(0,1)))
    outputs={s:s[2] for s in states}
    table={}
    alphabet=set().union(*(set(r) for r in RAW.values()))
    for state in states:
        line,bol,value=state
        for ch,top in product(alphabet,(0,1,2)):
            sign=int(ch==45)
            idx=line-FIRST if bol else -1
            op=('stay',)
            if idx==1 and (mode!='bad_open' or not sign):
                op=('push',1)
            if idx==2 and mode=='hidden' and sign:
                op=('push',2)
            if idx==3 and top:
                op=('pop',)
            if idx==4:
                op=('push',2)
            dest=(min(end,line+int(ch==10)),ch==10,sign if idx==0 else value)
            table[state,top,ch]=(dest,*op)
    return table,(0,True,0),0,outputs

def replay(raw,m):
    table,q,bottom,outs=m
    stack=[(bottom,None)]
    line=0
    bol=True
    bad=None
    for offset,ch in enumerate(raw):
        idx=line-FIRST if bol else -1
        top,mark=stack[-1]
        step=table[q,top,ch]
        op=step[1]
        tag=2 if idx==1 else None
        if bad is None:
            if idx==1 and op!='push' or idx==3 and (mark!=2 or op!='pop') or idx not in (1,3) and op=='pop' and mark is not None:
                bad=offset
        if op=='push':
            stack.append((step[2],tag))
        if op=='pop':
            stack.pop()
        q=step[0]
        bol=ch==10
        line+=bol
    return bad,outs[q],stack

def check(mode,occ=(),ids=(),wanted=None):
    chart=compile_pins(CS,N,ALIASES,occurrence_pins=occ,id_pins=ids)
    edges,s,t,events=chart
    m=machine(mode)
    vals={raw:replay(raw,m) for k,raw in RAW.items() if legal(k,occ,ids)}
    bad={raw:info[0] for raw,info in vals.items() if info[0] is not None}
    good={info[1] for info in vals.values() if info[0] is None}
    expected='unaligned' if bad else 'empty' if not vals else 'pair' if len(good)==2 else 'constant'
    assert expected==wanted
    res=probe(edges,s,t,*m,events,predict=lambda raw:vals[raw][1],promised=True)
    assert res['status']==expected,(mode,res['status'],expected)
    if mode=='hidden' and not occ and not ids:
        assert good=={0,1} and bad
    if expected=='unaligned':
        w=res['witness']
        raw=w['physical']
        path=w['path']
        at=s
        for j in path:
            u,_,v=edges[j]
            assert u==at
            at=v
        assert at==t and bytes(edges[i][1] for i in path)==raw
        prefix=w['prefix_path']
        assert prefix==path[:len(prefix)] and prefix[-1]==w['edge']
        assert raw in bad and bad[raw]==len(prefix)-1
    if expected=='constant':
        assert good=={res['value']}
    if expected=='pair':
        assert {vals[x['physical']][1] for x in res['samples']}=={0,1}
        assert all(len(info[2])>1 for info in vals.values())
    for bits in [(),(0,),(0,1),(1,1,0,0),(0,0,0,0)]:
        raw=complete_prefix(CS,N,ALIASES,bits,occurrence_pins=occ,id_pins=ids)
        options={r for k,r in RAW.items() if legal(k,occ,ids) and all((k>>i)&1==v for i,v in enumerate(bits))}
        assert (raw in options) if options else (raw is None)
    if not occ and not ids:
        for cap in ('fact_cap','step_cap'):
            assert probe(edges,s,t,*m,events,promised=True,**{cap:0})['status']=='unknown'

def main():
    check('ordinary',wanted='pair')
    check('bad_open',wanted='unaligned')
    check('bad_open',[(3,1)],wanted='pair')
    check('bad_open',[(3,1)],[(1,1)],wanted='constant')
    check('bad_open',[(3,1)],[(2,1)],wanted='empty')
    check('ordinary',[(2,1),(2,0)],wanted='empty')
    check('hidden',wanted='unaligned')
    check('hidden',[(2,1),(3,1)],wanted='unaligned')
    check('hidden',[(2,0)],wanted='pair')
    print('9 signed/pinned physical fibres: exact verdicts, first mismatch bytes, global pair control, empty pins, leftover neutral frame and caps passed')
if __name__=='__main__':
    main()
