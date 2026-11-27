from padding_cnf import encode
from stack_padding import constant_dpda,padding_dag,palindrome_dpda
from stack_probe import probe

def paths(graph):
    es,s,t=graph;pending=[(s,b'')];out=set();by={}
    for u,b,v in es:by.setdefault(u,[]).append((b,v))
    while pending:
        u,raw=pending.pop()
        if u==t:out.add(raw);continue
        pending.extend((v,raw+bytes([b])) for b,v in by.get(u,[]))
    return out

def cnf(raw):
    lines=raw.splitlines();n,k=map(int,lines[0].split()[2:])
    cs=[tuple(map(int,l.split()[:-1])) for l in lines[1:]]
    assert k==len(cs)
    return n,cs

def sat(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)

def physical_bit(raw):
    n,cs=cnf(raw);assert n==14 and all(not sat(cs[:8],x<<2) for x in range(8))
    k=sum((r[0]<0)<<i for i,r in enumerate(cs[-3:]))
    return int(k>=4 and (k&1)==((k>>1)&1))

def follow(M,raw):
    T,q,bottom,out=M;stack=[bottom]
    for b in raw:
        q,act,*args=T[q,stack[-1],b]
        if act=='push':stack.extend(args)
        if act=='pop':assert len(stack)>1;stack.pop()
    return out[q]

def run(g,M,want,external=None,**kw):
    es,s,t=g;log=[]
    def fn(raw):
        log.append(raw);return follow(M,raw) if external is None else external(raw)
    r=probe(es,s,t,*M,predict=fn,**kw);assert r['status']==want,(r,want)
    assert log==[h['physical'] for h in r['samples']]
    for h in r['samples']:
        u=s;raw=[]
        for j in h['path']:
            a,b,v=es[j];assert a==u;u=v;raw.append(b)
        assert u==t and bytes(raw)==h['physical'] and follow(M,bytes(raw))==h['table_output']
    if want=='pair':assert len(set(log))==2 and {h['prediction'] for h in r['samples']}=={0,1}
    return r

def main():
    g=padding_dag([],2);M=palindrome_dpda([],2);expected={encode([],2,k) for k in range(8)}
    assert paths(g)==expected
    assert {b for b in expected if follow(M,b)}=={b for b in expected if physical_bit(b)}
    r=run(g,M,'pair',physical_bit)
    print('physical',len(expected),r['facts'],r['steps'],[len(s['physical']) for s in r['samples']])
    for bit in (0,1):assert run(g,constant_dpda(bit),'constant',promised=True)['value']==bit
    run(g,constant_dpda(1),'unknown')
    assert run(g,constant_dpda(1),'unknown',lambda b:0,promised=True)['reason']=='prediction mismatch'
    for kw in ({'fact_cap':0},{'step_cap':0}):assert run(g,M,'unknown',**kw)['reason']=='cap'
    assert not run(([],0,1),constant_dpda(0),'empty')['samples']
    assert run(([],0,0),constant_dpda(1),'constant',promised=True)['samples'][0]['physical']==b''
    # Two distinct callers enter the same child; output depends on the restored top.
    es=[(0,65,1),(0,66,1),(1,67,2),(2,68,3),(3,69,4),(0,65,1)]
    T={(q,a,b):(q,'stay') for q in (0,1) for a in range(4) for b in range(65,70)}
    for q in (0,1):
        for a in range(4):
            for b in (65,66,67):T[q,a,b]=(q,'push',b-64)
            if a:T[q,a,68]=(q,'pop')
            T[q,a,69]=(int(a==2),'stay')
    M=T,0,0,{0:0,1:1}
    r=run((es,0,4),M,'pair',lambda raw:int(raw==b'BCDE'))
    assert {s['physical'] for s in r['samples']}=={b'ACDE',b'BCDE'}
    print('caller reuse and leftover stack',r['facts'],r['steps'])
    for kind in ('underflow','missing'):
        bad=dict(T)
        if kind=='underflow':bad[0,0,68]=(0,'pop')
        else:del bad[0,0,68]
        try:probe(es,0,4,bad,0,0,{0:0,1:1})
        except ValueError:pass
        else:raise AssertionError(kind)
    for raw,value in ((b'p cnf 1 1\n1 0\n',1),(b'p cnf 1 2\n1 0\n-1 0\n',0)):
        n,cs=cnf(raw);assert int(any(sat(cs,x) for x in range(1<<n)))==value
        r=run(([(j,b,j+1) for j,b in enumerate(raw)],0,len(raw)),constant_dpda(value),'constant',promised=True)
        assert r['samples'][0]['physical']==raw
    print('cap, empty, epsilon, mismatch, invalid transitions and original CNF replay passed')

if __name__=='__main__':main()
