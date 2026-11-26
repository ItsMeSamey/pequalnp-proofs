from verify import *
def check(a,b,t,c):
    arm,=inside(b&~a)
    active=[(lc[a] if a>>i&1 else alln)&(lc[b] if b>>i&1 else alln) for i in range(7)]
    safe=[sum(1<<p for p in inside(T) if points[p]&active[i]) for i,T in enumerate(ss)]
    hit=[pc[q] for q in safe]
    idle=set(inside(127^(a|b)))
    # Every idle output may need both retained-guard companions t,v, or
    # one arm plus a different idle ordinary companion.
    for i in idle:
        for j,k in combinations((idle-{i})|{t,arm},2):
            assert all(m&hit[j]&hit[k] for m in pairs[i]),(a,b,i,j,k)
    for i in idle:
        for j,k in ((t,arm),(arm,t)):
            assert all(m&hit[k]&hit[i] for m in pairs[j])
    # Opposite-arm companion and the central-output tracing labels.
    for i,j in [(t,arm),(arm,t),(c,t),(c,arm)]:
        assert all(m&hit[j] for m in pairs[i])
    assert sum((s^q).bit_count() for s,q in zip(ss,safe))<=4
if __name__=='__main__':
 checked=0
 for a,b in combinations([x for x in range(128) if x.bit_count()==2],2):
    if not a&b:continue
    c,=inside(a&b);t,=inside(a&~b);check(a,b,t,c);checked+=1
 print(checked,'triple-block raw neg witness families')
