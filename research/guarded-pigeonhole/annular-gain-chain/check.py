from itertools import combinations
import random

def allowed(a,b):
    return len({a[v]^b[v] for v in a.keys()&b.keys()})<=1

def test_path(stars,s,t):
    # Singleton root stars are separately named even if an input edge is itself a singleton.
    allstars=[{s:0}]+stars+[{t:0}]
    def rec(path):
        if path[-1]==len(allstars)-1:return True
        for j,b in enumerate(allstars):
            if j in path:continue
            a=allstars[path[-1]]
            if not a.keys()&b.keys() or not allowed(a,b):continue
            if any(allstars[i].keys()&b.keys() for i in path[:-1]):continue
            if rec(path+[j]):return True
        return False
    return rec([0])

def brute(stars,s,t):
    for mask in range(1<<len(stars)):
        selected=[h for i,h in enumerate(stars) if mask>>i&1]
        value={s:0}
        for _ in selected:
            for h in selected:
                common=value.keys()&h.keys()
                if not common:continue
                v=next(iter(common)); off=value[v]^h[v]
                if any(value[w]!=(off^h[w]) for w in common):break
                value.update({w:off^z for w,z in h.items()})
            else:continue
            break
        else:
            if t in value:return True
    return False

if __name__=='__main__':
    rng=random.Random(321);yes=0
    for i in range(1000):
        stars=[{v:rng.randrange(2) for v in rng.sample(range(7),rng.randrange(1,4))} for _ in range(rng.randrange(9))]
        ans=test_path(stars,0,1);assert ans==brute(stars,0,1);yes+=ans
    print('1000 cases verified, YES',yes)
    a={0:0,2:0,3:0};b={1:0,2:0,3:1}
    assert not test_path([a,b],0,1)
    assert not test_path([a,b,{2:0,4:0,5:0}],0,1)
