"""Full-cube structural audit of the three-parameter pendant net."""
from itertools import combinations, permutations


def build(p, d, z, split=None):
    sizes = (p, d, z)
    if any(type(k) is not int or k < 1 for k in sizes):
        raise ValueError("positive pendant counts required")
    a, b, h = 0, 1, 2
    P = list(range(3,3+p))
    D = list(range(3+p,3+p+d))
    Z = list(range(3+p+d,3+p+d+z))
    n = 3+sum(sizes)
    gates = []
    def gate(op, left, right):
        gates.append((op,left,right))
        return n+len(gates)-1
    def union(pins):
        out = pins[0]
        for pin in pins[1:]:
            out = gate("or",out,pin)
        return out
    if split is None:
        E = union([b]+P)
        projected = None
    else:
        if not 0 < split < p:
            raise ValueError("both split children must be nonempty")
        left = union([b]+P[:split])
        right = union(P[split:])
        E = gate("or",left,right)
        projected = (left,right)
    B = union([a]+D)
    K = union([a,b])
    J = gate("and",E,B)
    H = gate("and",J,K)
    ordinary = gate("and",h,union([K]+Z))
    output = gate("or",H,ordinary)
    edges = set(combinations((a,b,h),2)) | {(a,x) for x in P} | {(b,x) for x in D} | {(h,x) for x in Z}
    return n,gates,output,edges,(P,D,Z),(E,B,K,J,H,ordinary),projected


def check(p,d,z,split=None):
    n,gates,out,edges,(P,D,Z),special,children=build(p,d,z,split)
    E,B,K,J,H,ordinary=special
    all_cases=(1<<(1<<n))-1
    vals=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
    raw=[{i} for i in range(n)]
    closure=[set() for _ in range(n)]
    ancestors=[set() for _ in range(n)]
    for i,(op,a,b) in enumerate(gates):
        assert a<n+i and b<n+i
        if op=="or":
            vals.append(vals[a]|vals[b])
            raw.append(raw[a]|raw[b])
            closure.append(closure[a]|closure[b]|{i})
        else:
            vals.append(vals[a]&vals[b])
            raw.append(set())
            closure.append(set())
        ancestors.append(ancestors[a]|ancestors[b]|{i})
    target=0
    for a,b in edges:
        target |= vals[a]&vals[b]
    assert vals[out]==target
    nbr=[{b for a,b in edges if a==v}|{a for a,b in edges if b==v} for v in range(n)]
    assert all(len(nbr[a]&nbr[b])<=1 for a,b in combinations(range(n),2))
    over=all_cases^target
    ands={i for i,(op,_,_) in enumerate(gates) if op=="and"}
    dirty={i for i in ands if vals[n+i]&over}
    tops=ands-dirty
    assert all(not(tops & (ancestors[gates[i][1]]|ancestors[gates[i][2]])) for i in ands)
    orn={i for i,(op,_,_) in enumerate(gates) if op=="or" and vals[n+i]&over}
    lam=set()
    star=set()
    c=0
    for i in tops:
        _,a,b=gates[i]
        c += int(not raw[a] or not raw[b])
        star.update(tuple(sorted((s,t))) for s in raw[a] for t in raw[b])
        for w,v in ((a,b),(b,a)):
            if len(raw[v])==1:
                lam.update(k for k in closure[w] if all(raw[x] for x in gates[k][1:]))
    exceptional=orn-lam
    residual=edges-star
    assert dirty=={J-n} and tops=={H-n,ordinary-n}
    assert (len(gates),len(exceptional),c,len(tops)-c)==(p+d+z+5,p+d,1,1)
    assert residual=={(0,1)}|{(0,x) for x in P}|{(1,x) for x in D}
    assert all(a in {0,1,2} or b in {0,1,2} for a,b in edges)
    assert {(0,P[0]),(1,D[0]),(2,Z[0])}<=edges
    if children is not None:
        def lost(child):
            projected=(vals[child]&vals[B]&vals[K])|vals[ordinary]
            return sum(1 for a,b in residual if not projected>>(1<<a|1<<b)&1)
        assert tuple(map(lost,children))==(p-split,split+d+1)
    return len(gates),len(exceptional),len(residual)


if __name__=="__main__":
    for p in range(1,5):
        for d in range(1,4):
            for z in range(1,4):
                check(p,d,z,split=p//2 if p>1 else None)
    print("36 full-cube parameter controls passed, including all structural counts and split losses")
    n,g,o,edges,*_=build(1,1,1)
    pairs=list(combinations(range(n),2))
    mask=min(sum(1<<i for i,(a,b) in enumerate(pairs) if tuple(sorted((p[a],p[b]))) in edges)
             for p in permutations(range(n)))
    assert mask==691
    print("Net canonical six-input graph mask:",mask)
