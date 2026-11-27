from itertools import product
from random import Random
from latin_dense_model import dense_model

def outcome(q, sites, pins, bits):
    vals = [bits[rep]^sign for rep,sign in sites]
    if not all(vals[i] for i in pins):
        return -1
    if any(not(vals[i] or vals[q+j] or vals[2*q+(i^j)])
           for i in range(q) for j in range(q)):
        return -1
    return vals.count(0)

if __name__ == '__main__':
    rng = Random(391)
    trials = 0
    for q in (1,2,4,8):
        for sample in range(24):
            n = min(7,3*q)
            sites = [(rng.randrange(n),rng.randrange(2)) for _ in range(3*q)]
            pins = [i for i in range(3*q) if rng.random()<.12]
            if sample<4 and q>1:
                h = rng.randrange(1,q)
                sites = [(rep,((h&(i%q)).bit_count()%2)^int(i//q==2))
                         for i,(rep,_) in enumerate(sites)]
                pins = []
            best = max(outcome(q,sites,pins,bits) for bits in product((0,1),repeat=n))
            for t in sorted(set((max(1,q//2),q,q+1))):
                result = dense_model(q,sites,pins,t)
                assert (result is not None)==(best>=q+t)
                if result is not None:
                    assert outcome(q,sites,pins,result)>=q+t
                trials += 1
    print(f'{trials} physical dense-target comparisons passed')
