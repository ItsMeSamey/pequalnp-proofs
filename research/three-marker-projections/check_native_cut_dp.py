from itertools import product
from random import Random
from native_cut_dp import solve

def joins(p,m,r,s):
    seen=set();i=r
    while i not in seen:
        if i==s:return True
        seen.add(i)
        i=p[3*(i//3)+(i%3+m[i//3])%3]
    return False

def run():
    rnd=Random(9051)
    for test in range(360):
        n=rnd.randrange(1,7);p=list(range(3*n));rnd.shuffle(p)
        menus=[rnd.choice([(0,1),(0,1,2),(1,),(0,2),(2,)]) for _ in range(n)]
        labels=list(range(n))
        rnd.shuffle(labels)
        while len(labels)>1:
            j=rnd.randrange(len(labels)-1)
            labels[j:j+2]=[(labels[j],labels[j+1])]
        r=rnd.randrange(3*n);s=rnd.randrange(3*n)
        want=any(joins(p,m,r,s) for m in product(*menus))
        ans=solve(p,menus,r,s,labels[0])
        assert (ans is not None)==want,(test,p,menus,r,s)
        if ans is not None:
            assert all(x in M for x,M in zip(ans,menus)) and joins(p,ans,r,s)
    print('360 closed-circuit oracle and physical witness comparisons passed')

if __name__=='__main__':run()
