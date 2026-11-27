"""Direct sheet-level routing, compared with the input/output predicate."""
from itertools import permutations
from random import Random


def rotate(x, gate, inverse):
    if x not in gate:
        return x
    return gate[(gate.index(x) + (-1 if inverse else 1)) % 3]


def physical(n, gates, masks, O):
    step = []
    for v in range(2*n):
        sheet,x=divmod(v,n)
        for g,gate in enumerate(gates):
            if masks[sheet] >> g & 1:
                x=rotate(x,gate,False)
        sheet ^= x in O
        for g in reversed(range(len(gates))):
            if masks[2+sheet] >> g & 1:
                x=rotate(x,gates[g],True)
        step.append(sheet*n+x)
    return step


def closed(step,n,I):
    # Roots lie at the seam before the network, on its two end cycles.
    if not I:
        return True
    feedback=list(range(2*n))
    for a,b in zip(I,I[1:]):
        feedback[a+n],feedback[b]=feedback[b],feedback[a+n]
    first,last=I[0],I[-1]+n
    x=first
    while True:
        if x==last:
            return True
        x=feedback[step[x]]
        if x==first:
            return False


def run():
    rng=Random(22463)
    count=yes=unequal=0
    for n in range(3,7):
        for trial in range(18):
            gates=[rng.sample(range(n),3) for _ in range(1+trial%4)]
            for mask in range(1<<len(gates)):
                seq=list(range(n))
                for g,gate in enumerate(gates):
                    if mask>>g&1:
                        seq=[rotate(v,gate,False) for v in seq]
                for om in range(1<<n):
                    O={v for v in range(n) if om>>v&1}
                    step=physical(n,gates,[mask]*4,O)
                    want=[(v+n)%(2*n) if seq[v%n] in O else v for v in range(2*n)]
                    if step!=want:
                        raise AssertionError('sheet mismatch')
                    for im in range(1<<n):
                        I=[v for v in range(n) if im>>v&1]
                        actual=closed(step,n,I)
                        truth=all(seq[i] in O for i in I)
                        if actual!=truth:
                            raise AssertionError((n,gates,mask,I,O))
                        count+=1
                        yes+=truth
                        unequal+=len(I)!=len(O)
    # An independent choice of one copied bit yields a spurious positive.
    bad=None
    n=3
    gates=[(0,1,2)]
    for I in permutations(range(n),2):
        for O in permutations(range(n),2):
            if any(closed(physical(n,gates,[s]*4,set(O)),n,I) for s in (0,1)):
                continue
            for s in (0,1):
                truth=closed(physical(n,gates,[s]*4,set(O)),n,I)
                for idx in range(4):
                    masks=[s]*4
                    masks[idx]^=1
                    if not truth and closed(physical(n,gates,masks,set(O)),n,I):
                        bad=I,O,masks
    if bad is None:
        raise AssertionError('missing mismatch control')
    print(count,'comparisons,',yes,'positive,',unequal,'unequal-size controls; untied false positive',bad)


if __name__=='__main__':
    run()
