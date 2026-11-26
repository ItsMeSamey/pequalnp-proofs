"""Independent direction capacity of single-pin continuation forests."""
from singleton_forests import forests
from math import prod

def capacity(tree):
    return sum(prod(capacity(child) for child in side) for side in tree)

if __name__ == '__main__':
    for d in range(1,7):
        caps=[prod(map(capacity,forest)) for forest in forests(d)]
        print(d,len(caps),sum(q<12 for q in caps),min(caps),max(caps),flush=True)
