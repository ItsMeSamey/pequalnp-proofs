from functools import lru_cache
from itertools import combinations,product
def check(b):
    full=(1<<(1<<b))-1
    bits=[sum(1<<i for i in range(1<<b) if i>>j&1) for j in range(b)]
    num=(1<<b)-1
    # m raw point subset; s subset of {T,U}; y number of shared occurrences.
    @lru_cache(None)
    def enum(m,s,y,Y):
        out={(0,0),(full,full)} # unused leaves are simulated by neutral constants
        if m.bit_count()+s.bit_count()+y==0:return out
        if m.bit_count()+s.bit_count()+y==1:
            if m:out.add((bits[m.bit_length()-1],)*2)
            elif s:out.add((full,0) if s==1 else (0,full))
            else:out.add(Y)
            return out
        for i in range(m+1):
            if i&~m:continue
            for j,k in product(range(s+1),range(y+1)):
                if j&~s:continue
                a=i,j,k;d=m^i,s^j,y-k
                if a>d or not any(a) or not any(d):continue
                for x,z in enum(*a,Y):
                    for w,h in enum(*d,Y):
                        out.add((x&w,z&h));out.add((x|w,z|h))
        return out
    outcomes=set()
    for i,s in product(range(num+1),range(4)):
        for Y in enum(i,s,0,(0,0)):
            outcomes.update(enum(num^i,3^s,2,Y))
    todo=outcomes.copy();initial=frozenset([*bits,0,full]);states={initial}
    for d in range(b+2):
        for v in states:todo.difference_update(product(v,v))
        if not todo or d==b+1:break
        states={s|{z} for s in states for x,y in combinations(s,2) for z in (x&y,x|y) if z not in s}
    print(b,len(outcomes),len(todo),sorted(todo)[:5],flush=True)
    return todo
if __name__=='__main__':
 for b in range(5):check(b)
