"""Direct NAND-port truth sums after the disjoint triple prefix."""
from itertools import product


def audit(n, gates):
    # Sources are ('w',input), ('z',earlier gate), or ('c',constant).
    g = len(gates)
    m = g + (n+2*g+1)//2
    padding = 2*m-4*g-n
    bits = lambda width: product((0,1), repeat=width)

    def resolve(source, word, outputs):
        tag, i = source
        return i if tag == 'c' else (word if tag == 'w' else outputs)[i]

    accepting = 0
    for word in bits(n):
        outputs = []
        for left,right in gates:
            outputs.append(1 ^ (resolve(left,word,outputs) & resolve(right,word,outputs)))
        accepting += outputs[-1]

    # The untouched next triple splits each prefix equally, even when
    # its ports happen to coincide in value with earlier ports.
    triples = list(bits(3))
    survivors = 8**m
    for j in range(m):
        ones = sum((a*b)^c for a,b,c in triples)
        assert ones == 4 and ((0*0)^1) == 1
        assert survivors*ones//8 == survivors//2
        survivors //= 2
    bins = [0,0]
    planted_answer = None
    for ports in bits(2*m):
        z = [1 ^ (ports[2*j] & ports[2*j+1]) for j in range(m)]
        word = ports[2*g:2*g+n]
        multipliers = ports[2*g+n:4*g+n]
        value = z[g-1]
        for j,gate in enumerate(gates):
            for side,source in enumerate(gate):
                i = 2*j+side
                value ^= multipliers[i] & (ports[i] ^ resolve(source,word,z))
        bins[value] += 1
        if not any(ports):
            planted_answer = value
    assert sum(bins) == survivors == 4**m
    assert bins[0]-bins[1] == 2**(2*g+padding)*(2**n-2*accepting)
    extracted = (2**n-(bins[0]-bins[1])//2**(2*g+padding))//2
    assert extracted == accepting and planted_answer == 1
    return accepting, int(bins[1] > bins[0])


if __name__ == '__main__':
    for n in (0,1,2):
        sources = [('c',0),('c',1)] + [('w',i) for i in range(n)]
        for gate in product(sources,repeat=2):
            audit(n,[gate])
    w = ('w',0),('w',1)
    # Two gates distinguish a gate's extracted NAND output from either port.
    assert audit(2,[w,(('z',0),('c',1))]) == (1,0)
    assert audit(2,[w]) == (3,1)
    assert audit(1,[(('w',0),('c',1))]) == (1,0)
    print('Planted labels, both bins, and extracted NAND counts agree.')
