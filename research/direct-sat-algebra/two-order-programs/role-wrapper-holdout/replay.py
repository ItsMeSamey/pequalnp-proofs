import collections,json,sys,time,signal
from pathlib import Path
from corpus import cases
from run import valid,fail
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent/'selector-proxy-native'))
import proxy
orig=proxy.CheckedTranslation.__call__
counts=collections.Counter()
def check(self,j,front,D,E,banks,selectors):
    if not orig(self,j,front,D,E,banks,selectors):return False
    a,sa=self.groups.key(j,front,D,banks,selectors)
    b,sb=self.groups.key(j,front,E,banks,selectors)
    shift=(sa^sb if a==b else proxy.certificate(front,proxy.from_forbidden(front,D),proxy.from_forbidden(front,E),self.groups.basis))
    assert shift is not None
    tail=[(s if mode==0 else -s,)+tuple(row) for i,s in enumerate(selectors[j:],j+1) for mode,bank in enumerate(banks[i]) for row in bank]
    assert all(not (shift>>(v-1)&1) for v in selectors[:j])
    # Signed row-set invariance, variable names retained. Scope-local
    # translation maps every forbidden word to another original row.
    signed={frozenset(row) for row in tail}
    flipped={frozenset(-l if shift>>(abs(l)-1)&1 else l for l in row) for row in tail}
    assert signed==flipped
    vs=sorted({abs(v) for row in tail for v in row})
    if len(vs)<=13:
        for w in range(1<<len(vs)):
            x=sum((w>>i&1)<<(v-1) for i,v in enumerate(vs))
            assert valid(tail,x)==valid(tail,x^shift)
        counts['tail_model_checks']+=1
    assert len(front)<=13
    for w in range(1<<len(front)):
        x=sum((w>>i&1)<<(v-1) for i,v in enumerate(front))
        assert not valid(D,x) or valid(E,x^shift)
    counts['acceptances']+=1
    return True
proxy.CheckedTranslation.__call__=check
signal.signal(signal.SIGALRM,fail)
for name,n,rows,_ in cases():
    for cap in (128,1):
        signal.alarm(3)
        try:proxy.solve_cnf(n,rows,state_cap=cap)
        finally:signal.alarm(0)
print(json.dumps(counts))
