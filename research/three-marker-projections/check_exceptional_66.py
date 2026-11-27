"""Replay the original two-root closed circuit with five hub swaps and one grant."""
from itertools import product

p = (3,7,5,4,6,8,9,0,11,1,2,10)
masks = (1,72,144,288,514,1024,2052)
swaps = [tuple(i for i in range(12) if m >> i & 1) for m in masks if m.bit_count()==2]
assert len(swaps)==5 and sum(masks)==4095

def joined(w, settings):
    aux = list(range(12))
    if settings[0]:
        aux[9:12] = [10,11,9]
    router = list(range(12))
    for enabled,(i,j) in zip(settings[1:],swaps):
        if enabled:
            router[i],router[j] = j,i
    nxt = [router[p[aux[i//3*3+(i%3+w[i//3])%3]]] for i in range(12)]
    orbit = {0}
    i = nxt[0]
    while i not in orbit:
        orbit.add(i)
        i = nxt[i]
    return 10 in orbit

if __name__=='__main__':
    seen=0
    for w in product(range(3), repeat=4):
        a,b,c,d=w
        expected = not ((a+c+d)%3==(b+c-d)%3==0 or
                        b==(a+1)%3 and c==(1-a)%3 and d in (0,1))
        mask_results = [joined(w,z) for z in product(range(2),repeat=6)]
        assert any(mask_results)==expected,w
        seen+=any(mask_results)
    assert seen==66
    print('81 words, 5184 original settings, 66 accepted')
