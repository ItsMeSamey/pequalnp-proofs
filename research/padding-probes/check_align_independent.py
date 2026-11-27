"""Independent native aligned-marker controls for serial 04 verification."""
from itertools import product
from stack_align import probe
from stack_align_padding import annotated_dag, aligned_fixture, hostile_fixture
from padding_cnf import encode

def simulate(raw, table, initial, bottom, outputs):
    state, stack = initial, [bottom]
    for byte in raw:
        action = table[state, stack[-1], byte]
        state, op = action[:2]
        if op == 'push':
            stack.append(action[2])
        if op == 'pop':
            stack.pop()
    return outputs[state]

def fixture(data, wanted):
    cs,n,aliases,table,initial,bottom,outputs=data
    edges,s,t,events=annotated_dag(cs,n,aliases)
    vals={}
    for key in range(1<<(n+1)):
        bits={}
        for j,a in enumerate(aliases):
            i,off=(abs(a),a<0) if isinstance(a,int) else a
            v=((key>>j)&1)^off
            if i in bits and bits[i]!=v:
                break
            bits[i]=v
        else:
            raw=encode(cs,n,key)
            vals[raw]=simulate(raw,table,initial,bottom,outputs)
    res=probe(edges,s,t,table,initial,bottom,outputs,events,predict=vals.__getitem__,promised=True)
    assert res['status']==wanted,(res['status'],wanted)
    if wanted=='pair':
        assert set(vals.values())=={0,1}
    if wanted=='constant':
        assert set(vals.values())=={res['value']}
    for sample in res['samples']:
        assert vals[sample['physical']]==sample['prediction']
        at=s
        for j in sample['path']:
            u,_,v=edges[j]
            assert u==at
            at=v
        assert at==t and bytes(edges[j][1] for j in sample['path'])==sample['physical']
    return set(vals.values())

def neutral():
    # A,a open outer; B,b open inner; C,c and D,d close them.
    layers=[b'Aa',b'P',b'Bb',b'P',b'Q',b'Cc',b'Q',b'Dd']
    edges=[];events={}
    for i,choices in enumerate(layers):
        for ch in choices:
            if i in (0,2,5,7):
                events[len(edges)]=('open' if i<3 else 'close',1 if i in (0,7) else 2,int(ch>=97))
            edges.append((i,ch,i+1))
    out={0:0,1:1}
    table={}
    for state,top,ch in product(out,(0,1,2),{ch for _,ch,_ in edges}):
        op=(('push',2) if ch==80 else ('push',1) if chr(ch).upper() in ('A','B') else
            ('pop',) if top else ('stay',))
        table[state,top,ch]=(1 if ch==97 else state,*op)
    def run(ev,**kw):
        return probe(edges,0,8,table,0,0,out,ev,predict=lambda raw:int(raw[0]==97),promised=True,**kw)
    res=run(events)
    assert res['status']=='pair'
    for x in res['samples']:
        r=x['physical']
        assert r[0] in b'Aa' and r[0]+3==r[7] and r[2]+1==r[5]
    for cap in ('step_cap','fact_cap'):
        assert run(events,**{cap:0})['status']=='unknown'
    for j,ev in events.items():
        if ev[0]=='close':
            bad=dict(events);bad[j]=('close',99,ev[2])
            assert run(bad)['status']=='unaligned'
            break
    bad={j:e for j,e in events.items() if e[0]!='close'}
    assert run(bad)['status']=='unaligned'
    for malformed in ({len(edges):('open',1,0)},{0:('open',1,2)}):
        try:
            run(malformed)
        except ValueError:
            continue
        raise AssertionError('invalid event accepted')

def main():
    neutral()
    assert fixture(aligned_fixture(2,mismatch=False,gate=False),'constant')=={1}
    assert fixture(aligned_fixture(2,mismatch=True,gate=False),'constant')=={0}
    fixture(aligned_fixture(2,mismatch=False,gate=True),'pair')
    fixture(hostile_fixture(2),'unaligned')
    try:
        annotated_dag([],3,[1,2,1,2])
    except ValueError:
        pass
    else:
        raise AssertionError('crossing syntax accepted')
    print('nested neutral frames, malformed events, caps, exact physical constants 1/0 and pair, crossing controls passed')
if __name__=='__main__':
    main()
