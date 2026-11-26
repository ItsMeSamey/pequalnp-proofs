from collections import Counter
from itertools import permutations,product
from six_accessory_kempe import test,orbit
C=range(3)
strings=list(product(C,repeat=6))
def proper_star(*colors):return len(set(colors))==3
def extends(s,i,j):
    a,b=s[:3],s[3:]
    # P4 left endpoint shore A, left center B, right center A, right endpoint B.
    for l,m,r in product(C,repeat=3):
        if (proper_star(l,*(a[k] for k in C if k!=i)) and proper_star(l,m,b[j])
            and proper_star(m,r,a[i]) and proper_star(r,*(b[k] for k in C if k!=j))):return True
    return False
allow=lambda s:len(set(s))==1 or (s[:3]==s[3:] and len(set(s[:3]))==3)
S={s for s in strings if all(s.count(c)%2==0 for c in C) and (Counter(s[:3])!=Counter(s[3:]) or allow(s))}
for n,k in [(99,17),(24,4),(6,1),(0,0)]:
    assert (len(S),len({orbit(s) for s in S}))==(n,k)
    S={s for s in S if test(S,s)}
T={s+s for s in permutations(C)}
for i,j in product(C,repeat=2):assert all(extends(s,i,j)==(i!=j) for s in T)
wrong=[s for s in strings if Counter(s[:3])==Counter(s[3:]) and not allow(s)]
for s in wrong:assert any(extends(s,i,i) for i in C),(s,'no P4')
print('99→24→6→0. All',len(wrong),'wrong balanced strings distinguished; all 54 desired-rainbow comparisons agree.')
