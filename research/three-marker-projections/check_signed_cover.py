from itertools import product

INPUT=(0,1,2,3,4,5,0,2,1,3,4,5)
OUTPUT=(0,2,1,3,5,4,3,4,5,0,1,2)
WORDS=list(product(range(3),repeat=4))

def wiring(switches):
    w=[None]*12
    for hub,bit in enumerate(switches):
        ins=[i for i,x in enumerate(INPUT) if x==hub]
        outs=[i for i,x in enumerate(OUTPUT) if x==hub]
        if bit:ins.reverse()
        for a,b in zip(outs,ins):w[a]=b
    return w

def orbit(w,word,start):
    reached=set()
    j=start
    while j not in reached:
        reached.add(j)
        j=w[(j//3)*3+(j%3+word[j//3])%3]
    return reached

if __name__=='__main__':
    settings=[wiring(b)for b in product((0,1),repeat=6)]
    caps=[wiring(x)for x in [(1,0,0,1,1,1),(1,1,1,1,0,0)]]
    sizes=[0,0]
    for word in WORDS:
        a,b,c,d=word
        nonzero=bool((a+c+d)%3 or (b+c-d)%3)
        reached=[orbit(w,word,0)for w in settings]
        assert any({1,2}<=r for r in reached)==nonzero
        assert any(1 in r for r in reached)==(nonzero or a==2)
        trials=[7 in orbit(w,word,6)for w in caps]
        assert any(trials)==nonzero
        for i,val in enumerate(trials):sizes[i]+=val
    assert sizes==[54,54]
    print('81 input words x 64 native router settings, two 54-word selectors')
