"""Four explicitly listed original five-AND prefixes on the official target."""
from h5_terminal_prefix import finish
from h5_raw_terminal import EDGES,target
N=[x for x in range(1024) if not target(x) and all(target(x|1<<i) for i in range(10) if not x>>i&1)]
F=sum(1<<x for x in range(1024) if target(x))
def check(c):
    def mask(*v):return sum(1<<i for i in v)
    pairs=[(mask(0,1),mask(4)),(mask(1,3),mask(2)),(mask(10,0),mask(4,6)),
           (mask(11,5),mask(2,6)),(mask(10,c),mask(11,4))]
    physical=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]
    available=physical[:];flags=[False]*10;bank={}
    def wire(s):
        if s.bit_count()==1:return physical[s.bit_length()-1]
        if s not in bank:
            value=0
            for i,v in enumerate(physical):
                if s>>i&1:value|=v
            bank[s]=value;available.append(value);flags.append(bool(s>>10))
        return bank[s]
    for a,b in pairs:
        h=wire(a)&wire(b)
        physical.append(h);available.append(h);flags.append(True)
    traces=[tuple(sum(1<<i for i,x in enumerate(tests) if v>>x&1) for tests in (EDGES,N)) for v in available]
    assert all(any(v>>x&1 for x in EDGES) and any(v>>x&1 for x in N) for v in physical[10:])
    ans=finish(traces,13,16,flags)
    def maximal(P):
        value=0;flag=False
        for (_,n),v,m in zip(traces,available,flags):
            if not n&~P:value|=v;flag|=m
        return value if flag else 0
    feasible=any(maximal(P)&maximal(65535^P)==F for P in range(32768))
    assert feasible==(ans is not None)
    return len(bank),ans
if __name__=='__main__':
    for c in (3,5,7,8):print(c,check(c))
