"""Independent physical truth, raw-key, Fourier-support and query receipt controls."""
from itertools import product
from padding_cnf import encode,parse,predict

def rows(raw):
    lines=raw.decode('ascii').splitlines()
    nt,mt=map(int,lines[0].split()[2:])
    cs=[tuple(map(int,line.split()[:-1])) for line in lines[1:]]
    assert len(cs)==mt and all(len({abs(x) for x in c})==3 for c in cs)
    assert all(1<=abs(x)<=nt for c in cs for x in c)
    return nt,cs

def sat(cs,word):
    return all(any(bool(word & (1<<(abs(v)-1)))==(v>0) for v in c) for c in cs)

def decode_key(raw,n):
    _,cs=rows(raw)
    return sum((c[0]<0)<<i for i,c in enumerate(cs[-(n+1):]))

def carrier_tests():
    # Empty challenge, seven clauses with a single planted assignment 5, and contradiction.
    forbid=lambda word: tuple(-j if (word>>(j-1))&1 else j for j in (1,2,3))
    unit=[forbid(x) for x in range(8) if x!=5]
    for n,cs in ((0,[]),(3,[]),(3,unit),(3,[forbid(x) for x in range(8)])):
        lengths=set()
        for key in range(1<<(n+1)):
            raw=encode(cs,n,key); lengths.add(len(raw))
            assert parse(raw)==(n,cs,key) and decode_key(raw,n)==key
            assert predict(raw)==int(bool(key>>n) and sat(cs,key))
            nt,physical=rows(raw)
            core=physical[len(cs):len(cs)+8]
            assert all(not sat(core,z<<n) for z in range(8))
            if n==0:assert not any(sat(physical,w) for w in range(1<<nt))
        assert len(lengths)==1
    for bad in (b'',encode([],0,0).replace(b' 6 ',b' 06 ')):
        try:parse(bad)
        except ValueError:pass
        else:raise AssertionError('malformed source accepted')
    return unit

def spectrum(m,f):
    return {a for a in range(1<<m) if
            sum(f(x)*(-1 if (a&x).bit_count()%2 else 1) for x in range(1<<m))}

def mod(a,b):
    while a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
    return a

def field_check(field):
    p=field['modulus'];d=field['degree'];q=1<<d
    assert q==field['size'] and p.bit_length()==d+1
    assert all(mod(p,b) for b in range(2,1<<(d//2+1)))
    def mul(a,b):
        z=0
        for i in range(d):
            if b>>i&1:z^=a<<i
        return mod(z,p)
    def period(a):
        v=1
        for j in range(1,q):
            v=mul(v,a)
            if v==1:return j
    assert any(period(a)==q-1 for a in range(1,q))

def walsh(unit):
    from walsh_probe import probe
    parity=lambda x:(-1)**(x.bit_count()%2)
    hit=lambda x:int(x==13)
    for name,cs,ref,fn,s,promise,want in (
      ('zero',[],lambda x:0,lambda b:0,0,True,'constant'),
      ('one',[],lambda x:1,lambda b:1,1,False,'unknown'),
      ('enabled',[],lambda x:x>>3,predict,2,True,'disagreement'),
      ('parity',[],parity,lambda b:parity(decode_key(b,3)),1,True,'disagreement'),
      ('dense',unit,hit,predict,16,True,'disagreement'),
      ('underbound',unit,hit,predict,0,False,'unknown')):
        support=spectrum(4,ref)
        if promise:assert len(support)<=s
        if name in ('dense','underbound'):assert len(support)==16
        emitted=[];seen=[]
        def make(k):
            b=encode(cs,3,k);emitted.append((k,b));return b
        def observe(b):
            seen.append(b);v=fn(b);assert v==ref(decode_key(b,3));return v
        r=probe(4,s,make,observe,promised=promise)
        assert r['status']==want and [b for _,b in emitted]==seen
        assert len({k for k,b in emitted})==len(seen)==r['calls']
        assert r['calls']==r['work']['construct_calls']==r['work']['predict_calls']
        assert len({len(b) for b in seen})==1 and r['physical_input_bytes']==sum(map(len,seen))
        field_check(r['field'])
        if want=='disagreement':
            assert r['keys'][0]==0 and len(set(r['predictions']))==2
            for b,k,v in zip(r['formulas'],r['keys'],r['predictions']):
                assert b==encode(cs,3,k) and decode_key(b,3)==k and v==ref(k)
        else:assert r['work']['pairs_examined']==r['field']['pair_bound']
        print('walsh',name,r['status'],r['calls'],r['physical_input_bytes'])
    for promise in (True,False):
        def bad(_):raise AssertionError('unexpected callback')
        r=probe(0,1,bad,bad,promised=promise)
        assert (r['status'],r['calls'],r['physical_input_bytes'])==('constant',0,0)
    seq=iter((0,1))
    try:probe(1,1,lambda x:bytes(bytearray([99])),lambda b:next(seq))
    except ValueError:pass
    else:raise AssertionError('identical physical bytes gave contrary answers')

def sentinel():
    from sentinel_probe import double_until_error,sentinel_flat_predictor
    for cap,R,want,last in ((None,3,'false_negative',4),(2,3,'unknown',2),
                             (0,0,'unknown',0),(7,0,'false_negative',1),(7,None,'unknown',4)):
        log=[]
        def fn(raw):
            log.append(raw)
            n,cs=rows(raw);b=len(cs)
            assert n==3*b and cs==[tuple(range(i,i+3)) for i in range(1,n+1,3)]
            if R is None:return True
            v=sentinel_flat_predictor(R)(raw);assert v==(b<=R);return v
        r=double_until_error(fn,max_clauses=cap)
        assert (r['status'],r['b'],r['calls'],r['input_bytes'])==(want,last,len(log),sum(map(len,log)))
        assert [len(rows(b)[1]) for b in log]==[1<<i for i in range(last.bit_length())]
        if last:assert r['formula']==log[-1] and sat(rows(log[-1])[1],r['witness'])
        else:assert r['formula'] is None and r['witness'] is None
        print('sentinel',R,cap,last,r['calls'],r['input_bytes'])
    try:double_until_error(lambda b:2,max_clauses=1)
    except ValueError:pass
    else:raise AssertionError('invalid predictor answer')

if __name__=='__main__':
    walsh(carrier_tests())
    sentinel()
