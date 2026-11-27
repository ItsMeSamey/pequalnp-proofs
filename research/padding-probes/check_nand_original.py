"""Frozen independent original NAND-stack checks, g=1 and 2."""
from itertools import product
from padding_cnf import encode, predict
from stack_nand import nand_challenge, nand_dpda, nand_dag
from stack_probe import probe

def follow(machine, raw):
    table, state, bottom, outputs = machine
    stack = [bottom]
    for byte in raw:
        state, op, *args = table[state, stack[-1], byte]
        if op == 'push':
            stack.append(args[0])
        elif op == 'pop':
            assert len(stack) > 1
            stack.pop()
        else:
            assert op == 'stay'
    return outputs[state]

def check(g):
    n = 3*g
    cs = nand_challenge(g)
    assert len(cs) == 4*g and all(len(c)==len({abs(v) for v in c})==3 for c in cs)
    machine = nand_dpda(g)
    edges, start, final = nand_dag(g)
    by = {}
    for u,b,v in edges:
        by.setdefault(u,[]).append((b,v))
    def paths(u,raw):
        if u==final:
            yield raw
        else:
            for b,v in by.get(u,[]):
                yield from paths(v,raw+bytes([b]))
    truth = []
    raw_keys = {}
    for key in range(2**(n+1)):
        raw = encode(cs,n,key)
        raw_keys[raw] = key
        lines = raw.splitlines()
        rows = [tuple(map(int,line.split())) for line in lines[1:]]
        assert lines[0]==f'p cnf {4*n+6} {4*g+8+n+1}'.encode()
        assert all(r[-1]==0 and len(r)==4 for r in rows)
        assert sum((r[0]<0)<<i for i,r in enumerate(rows[-(n+1):]))==key
        assert len({r[:3] for r in rows[4*g:4*g+8]})==8
        assert all(tuple(map(abs,r[:3]))==(n+1,n+2,n+3) for r in rows[4*g:4*g+8])
        bit = lambda i:(key>>i)&1
        graph = all(bit(n-i-1)==1-bit(2*i)*bit(2*i+1) for i in range(g))
        sat = all(any(bit(abs(v)-1)==(v>0) for v in r[:3]) for r in rows[:4*g])
        assert sat==graph
        ans = int(graph and bit(n))
        assert predict(raw)==follow(machine,raw)==ans
        if bit(n):
            truth.append(ans)
    assert set(paths(start,b''))==set(raw_keys) and len(raw_keys)==2**(n+1)
    support = sum(sum(y*(-1)**((x&a).bit_count()%2) for x,y in enumerate(truth))!=0 for a in range(2**n))
    residuals = {tuple(truth[p | (s<<(2*g))] for s in range(2**g)) for p in range(2**(2*g))}
    assert support==5**g and len(residuals)==2**g and all(sum(r)==1 for r in residuals)
    r = probe(edges,start,final,*machine,predict=predict)
    assert r['status']=='pair' and {s['prediction'] for s in r['samples']}=={0,1}
    keys = []
    for s in r['samples']:
        u=start
        buf=bytearray()
        for j in s['path']:
            a,b,v=edges[j]
            assert a==u
            u=v
            buf.append(b)
        raw=bytes(buf)
        assert u==final and raw==s['physical']
        assert predict(raw)==s['prediction']==s['table_output']==follow(machine,raw)
        keys.append(raw_keys[raw])
    print(g,len(cs),len(raw_keys),sum(truth),support,len(residuals),keys,r['facts'],r['steps'])

for blocks in (1,2):
    check(blocks)
