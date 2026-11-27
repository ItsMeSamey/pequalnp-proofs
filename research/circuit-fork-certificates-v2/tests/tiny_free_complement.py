"""Check a physical complementary selector against the scalar fork engine."""
from collections import Counter
from itertools import product
import fork_certificate as engine


def check(ok, message):
    if not ok:
        raise ValueError(message)


def reject(action, reason):
    try:
        action()
    except ValueError as exc:
        check(reason in str(exc), 'unexpected rejection: '+str(exc))
        return
    raise ValueError('accepted a false exclusion')


def replay(x, gates):
    wires = [x & 1, 1-(x & 1), x>>1 & 1, x>>2 & 1]
    for op,a,b in gates:
        if op=='not':
            wires.append(1-wires[a])
        else:
            wires.append(wires[a]&wires[b] if op=='and' else wires[a]|wires[b])
    return wires[-1]


def dirs(care, j):
    return {y for x,y in care.items() if not x&(1<<j) and care.get(x|(1<<j))==1-y}


def feasible(care, model, gates):
    n=len(model['literals'])
    cert=engine.make_certificate(care,n,model,gates+model['fixed_cost'],[])
    reject(lambda:engine.verify_case(care,n,model,cert),'uncovered topology')


def main():
    both={'literals':['both_live','positive','positive'],'fixed_cost':1}
    mux=[('and',0,2),('and',1,3),('or',4,5)]
    care={x:replay(x,mux) for x in range(8)}
    check(dirs(care,0)=={0,1},'selector should be binate')
    uses=Counter(w for op,a,b in mux for w in (a,b))
    check(all(uses[w]==1 for w in range(6)),'no fork in physical MUX')
    _,bits,outside,live,_=engine.prepare(care,3,both)
    check(bits==[] and outside==7 and live==4,'conditioned MUX classification')
    feasible(care,both,3)
    wrong={'literals':['positive']*3,'fixed_cost':0}
    plan=[dict(positive=0,signed=0,ordered=True,partitions=0)]
    cert=engine.make_certificate(care,3,wrong,3,plan)
    check(engine.verify_case(care,3,wrong,cert)['total_lower_bound']==4,'positive-only contrast')
    reject(lambda:engine.verify_case(care,3,both,cert),'mismatch')
    # On an independent pair AND may reach 1; both legal complementary rows give 0.
    independent={p&q for p,q in product((0,1),repeat=2)}
    linked={replay(x,[('and',0,1)]) for x in range(8)}
    check(independent=={0,1} and linked=={0},'independent-selector counterexample')
    negative={'literals':['negative','positive','positive'],'fixed_cost':1}
    neg={x:replay(x,[('and',1,2)]) for x in range(8)}
    table,bits,_,live,_=engine.prepare(neg,3,negative)
    check(table=={x^1:y for x,y in neg.items()} and live==2 and not bits,'negative-only basis')
    feasible(neg,negative,1)
    neither={x:replay(x,[('or',2,3)]) for x in range(8)}
    check(all(neither[x]==neither[x^1] for x in neither),'unneeded selector')
    feasible({x>>1:y for x,y in neither.items()},{'literals':['positive']*2,'fixed_cost':1},1)
    check(any(care[x]!=care[x^1] for x in care),'MUX cannot drop both selector taps')
    # When x is true the data circuit is XOR(y,z); neither data source has
    # a free inverse. Both have physical forks feeding OR and AND.
    selector_xor=[('or',2,3),('and',2,3),('not',5,5),('and',4,6),
                  ('and',0,7),('and',1,3),('or',8,9)]
    xcare={x:replay(x,selector_xor) for x in range(8)}
    table,bits,outside,_,_=engine.prepare(xcare,3,both)
    check(bits==[1,2] and outside==1,'only the selector is a fixed outside coordinate')
    edges=engine.orientation_witnesses(table,bits,outside)
    general,positive=engine.derive_edges(table,bits,outside,edges)
    check(6 in general and 6 in positive,'XOR data pair requires separate fork groups')
    check(engine.ordered_filter(table,outside)(((2,False),(4,False))),'actual data forks survive')
    feasible(xcare,both,len(selector_xor))
    count=0
    for a,b in ((2,3),(3,2)):
        for p,q,r in product(('and','or'),repeat=3):
            gs=[(p,0,a),(q,1,b),(r,4,5)]
            full={x:replay(x,gs) for x in range(8)}
            for removed in (None,0,3,5):
                partial={x:y for x,y in full.items() if x!=removed}
                _,bits,outside,live,_=engine.prepare(partial,3,both)
                check(outside&1 and 0 not in bits,'selector must remain conditioned')
                check(live==2+sum(bool(dirs(partial,j)) for j in (1,2)),'partial live sources')
                feasible(partial,both,3)
                count+=1
    print('free-complement checks passed:',count,'enumerated full/partial tables')


if __name__=='__main__':
    main()
