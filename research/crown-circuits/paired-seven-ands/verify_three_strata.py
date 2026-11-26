"""Check physical maps, zero results, and the complete anchored-root ledger."""
from pathlib import Path
from collections import Counter
from three_iso_certificate import mapping

base=Path(__file__).resolve().parent
def rows(name):
    data=(base/name).read_text()
    assert data.endswith('\n')
    return [line.split() for line in data.splitlines()]

def check(cost):
    catalog={int(i):tuple(map(int,(a,b,c))) for i,a,b,c,fee in rows('three-filtered-catalog.tsv') if int(fee)==cost}
    counts={int(i):int(n) for i,fee,j,n in rows('three-hard-root-counts.tsv')}
    rawroots=Counter(int(i) for i,k in rows('three-hard-roots.tsv'))
    assert all(n==rawroots[i] for i,n in counts.items())
    names=('zero','one','two','three')
    rep={}
    for file,*raw in rows(f'three-cost-{names[cost]}-representatives.tsv'):
        r=list(map(int,raw))
        assert not r[-1] and r[0] in catalog
        if '-a-' in file or '-iso-' in file:
            assert r[2]==counts[r[0]] and r[2]>0
        rep[file,r[0]]=True
    checked=set()
    for i,file,j,*bits in rows(f'three-cost-{names[cost]}-permutations.tsv'):
        i,j=int(i),int(j)
        perm,flip=mapping(catalog[i],catalog[j])
        assert perm+flip==list(map(int,bits)) and (file,j) in rep and i not in checked
        checked.add(i)
    assert checked==set(catalog)
    print(cost,len(checked),len(rep),'physical catalog, representatives and roots agree')

if __name__=='__main__':
    import sys
    for c in sys.argv[1:]:check(int(c))
