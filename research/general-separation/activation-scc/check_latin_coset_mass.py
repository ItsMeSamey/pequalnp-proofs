from collections import Counter

def multiply(a,b):
    c=0
    while b:
        if b&1:
            c ^= a
        b >>= 1
        a <<= 1
        if a&32:
            a ^= 0b100101
    return c

def check():
    steps = {x | (multiply(multiply(x,x),x)<<5) for x in range(1,32)}
    assert len(steps)==31 and not any((x^y) in steps for x in steps for y in steps)
    values = Counter(sum(1-2*((u&x).bit_count()%2) for x in steps) for u in range(1,1024))
    assert values == {-9:186,-1:527,7:310}
    print('31 points, no sum triples, nontrivial character histogram', dict(sorted(values.items())))

if __name__=='__main__':
    check()
