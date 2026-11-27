"""List every strictly larger opposite function G when a raw OR filters the output."""
from collections import Counter

EDGES=(6,24,17,33,66,132,264,528,160,640,576,320,288)
def target(x):
    return any(x&e==e for e in EDGES)

def targets():
    for z in range(1024):
        outside=[1<<i for i in range(10) if not z>>i&1]
        if target(z) or any(not target(z|a) for a in outside):
            continue
        extra=[w for w in range(1024) if not w&~z and all(target(w|a) for a in outside)]
        for bits in range(1,1<<len(extra)):
            accepted={w for i,w in enumerate(extra) if bits>>i&1}
            if any(w&v==w and v not in accepted for w in accepted for v in extra):
                continue
            g=[target(x) or x in accepted for x in range(1024)]
            assert all(not g[x] or all(g[x|(1<<i)] for i in range(10)) for x in range(1024))
            assert all((g[x] and bool(x&~z))==target(x) for x in range(1024))
            yield z,accepted

if __name__=='__main__':
    rows=list(targets())
    print(len(rows),len({z for z,_ in rows}),min(w.bit_count() for _,a in rows for w in a))
