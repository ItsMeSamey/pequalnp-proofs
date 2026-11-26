from functools import lru_cache
from itertools import combinations
def audit(n):
    full=(1<<(1<<n))-1
    leaves=tuple(sum(1<<row for row in range(1<<n) if row>>p&1) for p in range(n))
    const=(0,full)
    @lru_cache(None)
    def trees(m):
        if m.bit_count()==1:return (m.bit_length()-1,)
        out=[]
        for l in range(1,m):
            r=m^l
            if l&m!=l or r<l:continue
            for a in trees(l):
                for b in trees(r):
                    for op in range(2):out.append((op,a,b))
        return tuple(out)
    def prunes(tr):
        if isinstance(tr,int):return set(const+(leaves[tr],))
        op,a,b=tr
        return {(x&y if op==0 else x|y) for x in prunes(a) for y in prunes(b)}
    targets=set()
    for tr in trees((1<<n)-1):
        vals=prunes(tr);targets.update(combinations(sorted(vals),2))
    todo={(a,b) for a,b in targets if a&b not in (a,b)}
    states={frozenset(const+leaves)}
    for i in range(n):
        for s in states:todo.difference_update(combinations(sorted(s),2))
        if not todo:break
        if i==n-1:break
        following=set()
        for s in states:
            for a,b in combinations(s,2):
                for x in (a&b,a|b):
                    if x not in s:following.add(s|{x})
        states=following
    print(n,len(targets),len(todo),sorted(todo)[:8])
for n in range(1,5):audit(n)
