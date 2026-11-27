from random import Random
from backward_bank import solve, estimate, plan


def native(n, gates, out, x):
    bits = 1 + 2*x
    for i, (a,b) in enumerate(gates):
        value = ((bits&a).bit_count()%2) * ((bits&b).bit_count()%2)
        bits += value << (n+1+i)
    return (bits&out).bit_count()%2


def verify(n, gates, out):
    gates = tuple(gates)
    e = estimate(n,gates,out)
    answer = solve(n,gates,out,budget=e)
    truth = [x for x in range(1<<n) if native(n,gates,out,x)]
    assert answer['cost']['accept_count'] == len(truth), (n,gates,out,answer,truth)
    assert answer['cost']['transitions'] <= e
    if truth:
        assert answer['status']=='sat' and answer['witness'] in truth
    else:
        assert answer['status']=='unsat'
    if e>1:
        assert solve(n,gates,out,budget=e-1)['status']=='skip'


if __name__=='__main__':
    rng=Random(24791)
    for _ in range(180):
        n=rng.randrange(0,7)
        gates=[]
        for j in range(rng.randrange(11)):
            gates.append(tuple(rng.getrandbits(n+j+1) for _ in range(2)))
        verify(n,gates,rng.getrandbits(n+len(gates)+1))
    for m in (3,8):
        n=4*m
        gates=tuple([(1<<(1+2*i),1<<(2+2*i)) for i in range(m)] +
                    [((1<<(1+2*m+2*i))^(1<<(1+n+i)),1<<(2+2*m+2*i)) for i in range(m)])
        out=((1<<m)-1)<<(1+n+m)
        e=estimate(n,gates,out)
        a=solve(n,gates,out,budget=e)
        assert a['cost']['accept_count']==(1<<(4*m-1))-(1<<(3*m-1))
        assert a['cost']['transitions']<=16*m
        print('m, cost, observed transitions:',m,e,a['cost']['transitions'])
    print('180 random original-circuit truth tables plus two growing-rank fixtures passed')
