"""Trace the constructive two-spoke extension and all five-cycle choices."""
from itertools import product
from random import Random


def cycles(p):
    unseen=set(p); parts=[]
    while unseen:
        x=min(unseen); part=[]
        while x in unseen:
            unseen.remove(x);part.append(x);x=p[x]
        parts.append(part)
    return parts


def rotation(seq):
    return dict(zip(seq,seq[1:]+seq[:1]))


def external_cycles(trees,hub):
    transition={}
    for root in trees:
        order=[]
        def walk(x):
            if isinstance(x,int):
                order.append(x)
            else:
                walk(x[0]);walk(x[1])
        walk(root)
        transition.update(rotation(order))
    k=rotation(hub)
    return len(cycles({a:k[transition[a]] for a in hub}))


def trial(rng, sizes):
    # Represent a rooted tree contour by its first leaf and a nested ordering
    # of the others. Each binary cherry either preserves or reverses its order.
    trees=[]; pairs=[]; nextval=0
    for p in sizes:
        first=nextval;nextval+=1
        trees.append(first)
        for i in range((p-1)//2):
            a=nextval;b=a+1;nextval+=2
            tree_index=len(trees)-1
            # Attaching a pendant cherry to any existing branch at a leaf is
            # encoded by replacing that leaf by (old,(a,b)) in its contour.
            old=rng.choice([first]+list(range(first+1,a)))
            pairs.append((tree_index,old,a,b))
    hub=rng.sample(range(nextval),nextval)
    live=set(trees)
    def sub(x,old,y):
        if isinstance(x,int):
            return y if x==old else x
        return tuple(sub(z,old,y) for z in x)
    for ti,old,a,b in pairs:
        live.update((a,b))
        for pair in ((a,b),(b,a)):
            proposed=trees.copy()
            proposed[ti]=sub(trees[ti],old,(old,pair))
            if external_cycles(proposed,[j for j in hub if j in live])==1:
                trees=proposed
                break
        else:
            raise AssertionError((sizes,hub,old,a,b))
    assert external_cycles(trees,hub)==1


def cycle_check():
    k=rotation([0,1,2,4,3]);histo={}
    for bits in product((0,1),repeat=5):
        a=[i for i in range(5) if bits[i]]
        b=[i for i in reversed(range(5)) if not bits[i]]
        p=rotation(a)|rotation(b)
        count=len(cycles({i:k[p[i]] for i in range(5)}))
        histo[count]=histo.get(count,0)+1
        assert count>1
    return histo


if __name__=='__main__':
    rng=Random(117)
    for _ in range(1000):
        trial(rng,[rng.choice([1,3,5,7,9]) for _ in range(rng.randrange(1,6))])
    print('1000 constructive odd-tree ensembles; five-cycle hub face-count histogram:',cycle_check())
