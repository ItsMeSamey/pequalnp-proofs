from insert import Enc, rows, seed
from random import Random
for trial in range(6):
    r=Random(1038+trial)
    enc=Enc()
    cuts=sorted(r.randrange(32) for _ in range(2))
    def add(x):enc.s.add_clause([x])
    def choose(v,i):add(v[i])
    for j,t in enumerate(cuts):
        for k,v in enumerate(enc.cut[j]):add(v if k>=t else -v)
    gates={}
    for j,t in enumerate(cuts):
        options=list(range(38+t))+list(range(69,69+j))
        a,b=sorted(r.choices(options,k=2));op=r.randrange(2)
        choose(enc.source[j][0],a);choose(enc.source[j][1],b)
        add(enc.ops[j] if op else -enc.ops[j])
        gates[69+j]=(op,a,b)
    for i,(op,a,b) in enumerate(seed):
        opts=[0]+[j+1 for j,t in enumerate(cuts) if t<=i]
        x,y=r.choices(opts,k=2)
        choose(enc.route[i][0],x);choose(enc.route[i][1],y)
        gates[38+i]=(op,[a,69,70][x],[b,69,70][y])
    o=trial%3;choose(enc.output,o)
    for i,row in enumerate(rows):
        w={j:row>>j&1 for j in range(38)}
        def ev(k):
            if k not in w:
                op,a,b=gates[k]
                w[k]=ev(a)&ev(b) if op else ev(a)|ev(b)
            return w[k]
        enc.add_row(i,bool(ev([68,69,70][o])))
    assert enc.s.solve()
    print('pass',trial,cuts,o,flush=True)
