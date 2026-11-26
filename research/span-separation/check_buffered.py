from itertools import combinations
def addr(s,x):return s|frozenset(a^x for a in s)
def family(cols,forced,base_dim):
    f={frozenset({0})}
    for i,x in enumerate(cols):
        nf={addr(s,x) for s in f}
        if i in forced:f=nf
        else:f|=nf
    return {frozenset(z for z in s if z<1<<base_dim) for s in f}
def check(E,b):
    base_dim=2
    i=base_dim;cols=[]
    for e in E:
        for _ in range(b+1):
            p=[0]+[1<<(i+j) for j in range(b)]+[e]
            cols.extend(x^y for x,y in zip(p,p[1:]))
            i+=b
    target=family(E,[],base_dim)
    n=len(cols);checks=0
    for nd in range(b+1):
        for dels in combinations(range(n),nd):
            rest=[j for j in range(n) if j not in dels]
            for nc in range(b-nd+1):
                for contracts in combinations(range(len(rest)),nc):
                    assert family([cols[j] for j in rest],contracts,base_dim)==target
                    checks+=1
    return checks
print(sum(check(E,b) for E,b in [([0,1,1],1),([1,2,3],1),([0],2),([2],2),([1,1],0)]))
