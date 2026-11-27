"""Generate original one-join U placements for four distinct linear raw triples."""
from collections import Counter,defaultdict
from itertools import combinations
from h5_prefix_nine_bank import indices,suffix
from h5_three_sink_leak_sets import EDGES,N,CASES

triples = [s for s in range(1024) if s.bit_count()==3]
covers = {s for s in range(1024) if all(s & edge for edge in EDGES)}
assert min(s.bit_count() for s in covers)==6
partners = {a: {b for b in triples if (a|b) in covers} for a in triples}

def placements():
    prefixes = defaultdict(set)
    def add(a,b,c,d,u):
        masks = (a,b,c,d)
        if any((x&y).bit_count()>1 for x,y in combinations(masks,2)):
            return
        key = (*sorted((a,b)),*sorted((c,d)))
        prefixes[key].add(u)
    for y in triples:
        for a,b in combinations(sorted(partners[y]),2):
            for d in triples:
                add(a,b,y,d,1024|y)
                add(y,d,a,b,2048|y)
    for a,b in combinations(triples,2):
        for c,d in combinations(sorted(partners[a] & partners[b]),2):
            add(a,b,c,d,3072)
    return prefixes

def allowed(scopes,u,leak):
    a,b,c,d = scopes
    for i in leak:
        row = N[i]
        hidden = (1024 if row&a and row&b else 0) | (2048 if row&c and row&d else 0)
        if (row|hidden)&u:
            return False
    return True

if __name__=='__main__':
    prefixes=placements()
    print('prefixes',len(prefixes),'placements',sum(map(len,prefixes.values())))
    hist=Counter()
    for scopes,us in sorted(prefixes.items()):
        for ix in indices:
            valid=[u for u in us if allowed(scopes,u,CASES[ix])]
            if not valid:
                hist[ix,'no_U']+=1
            else:
                hist[ix,suffix(scopes,ix)]+=1
    for ix in indices:
        print(ix,sorted((s,n) for (j,s),n in hist.items() if j==ix))
