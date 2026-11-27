"""Defect witness construction for fixed occupancies; bounded overlap/readout controls.

Each edge is (i,j,table) where bit 4*s+d of table admits occupancy s and defect
d, both low-bit-first in endpoint order. No private vertices are enumerated.
"""
from itertools import combinations, product
from random import Random
from collections import deque


def bits(x):
    while x:
        b=x&-x
        yield b.bit_length()-1
        x ^= b


def fixed(rows,c,edges,w):
    """Polynomial fixed-occupancy solver; returns one two-bit defect per edge or None."""
    required = (c ^ sum(((row&w).bit_count()%2)<<i for i,row in enumerate(rows))) & w
    data = []
    equal = [[] for _ in rows]
    resources = []
    for k,(i,j,table) in enumerate(edges):
        s = ((w>>i)&1) | (((w>>j)&1)<<1)
        options = {d&s:d for d in range(4) if table>>(4*s+d)&1}
        if not options:
            return None
        base = next(iter(options))
        if len(options)==3:
            base = next(d for d in options if d^1 in options and d^2 in options)
        data.append([base,options])
        required ^= ((base&1)<<i) | ((base>>1)<<j)
        if len(options)==3:
            resources.append([(i,k,1),(j,k,2)])
        elif len(options)==4:
            resources.extend([[(i,k,1)],[(j,k,2)]])
        elif len(options)==2:
            other = next(d for d in options if d!=base)
            direction = base ^ other
            if direction==3:
                equal[i].append((j,k))
                equal[j].append((i,k))
            else:
                resources.append([(i if direction==1 else j,k,direction)])
    comp = {}
    trees=[]
    for root in bits(w):
        if root in comp:
            continue
        cid=len(trees)
        comp[root]=cid
        order=[root]
        tree=[]
        for v in order:
            for u,k in equal[v]:
                if u not in comp:
                    comp[u]=cid
                    tree.append((u,v,k))
                    order.append(u)
        trees.append((order,tree))
    demands=[j for j,(verts,_) in enumerate(trees)
             if sum((required>>i)&1 for i in verts)%2]
    incident=[[] for _ in trees]
    for key,ends in enumerate(resources):
        for v,k,d in ends:
            incident[comp[v]].append((key,v,k,d))
    # Alternating paths match distinct available defect resources to odd components.
    owners={}
    assignment={}
    for root in demands:
        prev={root:None}
        queue=deque([root])
        hit=None
        while queue and hit is None:
            j=queue.popleft()
            for item in incident[j]:
                owner=owners.get(item[0])
                if owner is None:
                    hit=(j,item)
                    break
                if owner not in prev:
                    prev[owner]=(j,item)
                    queue.append(owner)
        if hit is None:
            return None
        while hit is not None:
            j,item=hit
            assignment[j]=item
            owners[item[0]]=j
            hit=prev[j]
    for _,v,k,d in assignment.values():
        data[k][0] ^= d
        required ^= 1<<v
    for _,tree in trees:
        for u,v,k in reversed(tree):
            if required>>u&1:
                required ^= (1<<u)|(1<<v)
                data[k][0] ^= 3
    assert not required
    return [options[d] for d,options in data]


def verify(rows,c,edges,w,defects):
    err = c ^ sum(((r&w).bit_count()%2)<<i for i,r in enumerate(rows))
    for (i,j,t),d in zip(edges,defects):
        s=((w>>i)&1)|(((w>>j)&1)<<1)
        if not t>>(4*s+d)&1:
            return False
        err ^= ((d&1)<<i)|((d>>1)<<j)
    return len(edges)==len(defects) and not err&w


def bounded(rows,c,edges,labels,target):
    for w in range(1<<len(rows)):
        read=0
        for i in bits(w):
            read ^= labels[i]
        if read==target:
            d=fixed(rows,c,edges,w)
            if d is not None:
                assert verify(rows,c,edges,w,d)
                return w,d
    return None


def test_defects():
    rng=Random(473928)
    tables = [65535 ^ sum(1<<j for j in holes) for r in range(3)
              for holes in combinations(range(16),r)]
    counts=[0,0,0]
    for tab in tables:
        edges=[(0,1,tab)]
        for w,c in product(range(4),repeat=2):
            ds=fixed([0,0],c,edges,w)
            exists=any(verify([0,0],c,edges,w,[d]) for d in range(4))
            assert (ds is not None)==exists
            if ds is not None:
                assert verify([0,0],c,edges,w,ds)
            counts[0]+=1
    for trial in range(120):
        n=2+trial%4
        ends=[(j,j+1) for j in range(n-1)]
        if trial%3:
            ends.append(rng.choice(ends))
        edges=[(i,j,rng.choice(tables)) for i,j in ends]
        rows=[0]*n
        for i,j in combinations(range(n),2):
            if rng.randrange(2):
                rows[i]|=1<<j
                rows[j]|=1<<i
        c=rng.randrange(1<<n)
        labels=[rng.randrange(4) for _ in rows]
        attainable=set()
        for w in range(1<<n):
            # Slow independent projection by XOR convolution over actual choices.
            states={0}
            for i,j,t in edges:
                s=((w>>i)&1)|(((w>>j)&1)<<1)
                local={(((d&1)<<i)|((d>>1)<<j))&w for d in range(4) if t>>(4*s+d)&1}
                states={x^y for x in states for y in local}
            need=(c ^ sum(((row&w).bit_count()%2)<<i for i,row in enumerate(rows)))&w
            ds=fixed(rows,c,edges,w)
            assert (ds is not None)==(need in states)
            if ds is not None:
                assert verify(rows,c,edges,w,ds)
                target=0
                for i in bits(w):
                    target^=labels[i]
                attainable.add(target)
            counts[1]+=1
        for target in range(4):
            assert (bounded(rows,c,edges,labels,target) is not None)==(target in attainable)
            counts[2]+=1
    print("fixed single-box, fixed mixed overlap, two-readout trials",counts)


if __name__=="__main__":
    test_defects()


def rank_one_failure(A,marked,unguarded,drift):
    """Exact rank-one obstruction for fixed head bits on one-sided signed guards."""
    live=(1<<len(A))-1
    while live:
        root=live&-live
        queue=list(bits(root))
        comp=root
        for i in queue:
            fresh=A[i]&~comp
            comp|=fresh
            queue.extend(bits(fresh))
        live &= ~comp
        if comp&marked and (comp&unguarded or comp&(drift^marked)):
            return False
    return True


def test_rank_one():
    rng=Random(52692)
    checked=0
    for n in range(1,8):
        for _ in range(75):
            A=[0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    A[i]|=1<<j
                    A[j]|=1<<i
            c=rng.randrange(1<<n)
            unguarded=rng.randrange(1<<n)
            marked=rng.randrange(1,1<<n)
            found=False
            for w in range(1<<n):
                if (w&marked).bit_count()%2 and all(
                    ((A[i]&w).bit_count() ^ (c>>i))&1==0 for i in bits(w&~unguarded)):
                    found=True
                    break
            assert rank_one_failure(A,marked,unguarded,c) != found
            checked+=1
    print("signed fixed-head rank-one fibers",checked)


if __name__=="__main__":
    test_rank_one()


def ordinary(table):
    for s in range(4):
        possible=[d for d in range(4) if table>>(4*s+d)&1]
        for bit in (1,2):
            if s&bit and len({d&bit for d in possible})<2:
                return False
    return True


def test_ordinary():
    tables=[65535^sum(1<<j for j in holes) for r in range(3)
            for holes in combinations(range(16),r)]
    plain=[t for t in tables if ordinary(t)]
    rng=Random(83920)
    trials=0
    for rep in range(24):
        n=2+rep%5
        pairs=[(j,j+1) for j in range(n-1)]
        if rep%3:
            pairs.append((0,n-1))
        edges=[(i,j,rng.choice(plain)) for i,j in pairs]
        # For a proper occupancy of a connected ordinary component, arbitrary
        # drift on occupied sites can be satisfied by propagating from a hole.
        for w in range((1<<n)-1):
            for c in range(1<<n):
                if c&~w:
                    continue
                ds=fixed([0]*n,c,edges,w)
                assert ds is not None and verify([0]*n,c,edges,w,ds)
                trials+=1
    print("ordinary tables",len(plain),"proper-component drift trials",trials)


if __name__=="__main__":
    test_ordinary()


def test_mixed_fiber():
    rng=Random(19425)
    count=0
    for rep in range(40):
        # T=0..2 singleton tails; Z=3,4 one nonsingleton ordinary component;
        # Y=5,6 has only independently adjustable head incidences.
        n=7
        rows=[0]*n
        for i,j in combinations(range(n),2):
            if rng.randrange(2):
                rows[i]|=1<<j
                rows[j]|=1<<i
        c=rng.randrange(128)
        beta=rng.randrange(1,8)
        edges=[(3,4,65535 ^ (1<<12) ^ (1<<15))]
        for i in range(3):
            for j in (5+i%2,):
                trigger,force=rng.randrange(2),rng.randrange(2)
                s=1|(trigger<<1)
                holes=[4*s+(1^force)+(h<<1) for h in (0,1)]
                edges.append((i,j,65535^sum(1<<v for v in holes)))
        for y in (0,32,64,96):
            any_extension=False
            sparse_extension=False
            for z in (0,8,16,24):
                drift=c ^ sum(((row&(y|z)).bit_count()%2)<<i for i,row in enumerate(rows))
                guarded=0
                for i,j,tab in edges[1:]:
                    s=1|(((y>>j)&1)<<1)
                    tail={d&1 for d in range(4) if tab>>(4*s+d)&1}
                    if len(tail)==1:
                        guarded|=1<<i
                        drift^=next(iter(tail))<<i
                fail=rank_one_failure([r&7 for r in rows[:3]],beta,7^guarded,drift)
                found=False
                for x in range(8):
                    if (x&beta).bit_count()%2:
                        w=x|y|z
                        ds=fixed(rows,c,edges,w)
                        if ds is not None:
                            assert verify(rows,c,edges,w,ds)
                            found=True
                            break
                if z!=24:
                    assert found != fail
                    sparse_extension |= found
                any_extension |= found
            assert any_extension==sparse_extension
            count+=1
    print("mixed ordinary/signed rank-one fibers with zero-or-unit probes",count)


if __name__=="__main__":
    test_mixed_fiber()


def test_profiles():
    count=0
    for component in ((0,1,2,3),(0,0,1,2),(0,0,1,1),(0,0,0,1),(0,0,0,0)):
        size=[component.count(k) for k in component]
        singles=[i for i in range(4) if size[i]==1]
        pairs=list(combinations(range(4),2))
        # Each singleton's release set is a nonempty set of one-head literals.
        for lists in product((1,2,3),repeat=len(singles)):
            releases=dict(zip(singles,lists))
            for labels in product(range(4),repeat=4):
                independent=[(i,j) for i,j in pairs if labels[i] and labels[j] and labels[i]!=labels[j]]
                if not independent:
                    continue
                count+=1
                def compatible(i,j):
                    if i in releases and j in releases:
                        return bool(releases[i]&releases[j])
                    return component[i]!=component[j] or size[i]>=3
                if any(compatible(i,j) for i,j in independent):
                    continue
                i,j=independent[0]
                if i in releases:
                    assert j in releases and {releases[i],releases[j]}=={1,2}
                    assert all(k in releases for k,v in enumerate(labels) if v)
                    for y in (1,2):
                        remaining={v for k,v in enumerate(labels) if v and not releases[k]&y}
                        assert len(remaining)<=1
                else:
                    assert size[i]==size[j]==2 and component[i]==component[j]
                    assert all(not v for k,v in enumerate(labels) if k not in (i,j))
    # Every ordinary occupancy-11 relation contains a complementary pair.
    tables=[65535^sum(1<<j for j in holes) for r in range(3)
            for holes in combinations(range(16),r)]
    sets={tuple(d for d in range(4) if t>>(12+d)&1) for t in tables if ordinary(t)}
    for a,b in product(sets,repeat=2):
        assert any((i^3) in a for i in a)
        K={i^j for i in a for j in b}
        lines={frozenset(p) for p in combinations(K,2)}
        assert set.union(*(set(p) for p in lines))==K
    print("four-site rank-two profiles",count,"ordinary pair-defect products",len(sets)**2)


if __name__=="__main__":
    test_profiles()
