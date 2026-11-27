from itertools import combinations
from modal_fibers import solve,build,apply_word

def direct_product(h):
    vs=[(i,a) for i in range(5) for a in range(h)]
    edges=[(i,j) for i,j in combinations(range(len(vs)),2)
           if vs[i][0]!=vs[j][0] and vs[i][1]!=vs[j][1]]
    return build(len(vs),edges),[range(i*h,(i+1)*h) for i in range(5)]

for h,result in ((4,'UNKNOWN'),(5,'UNSAT')):
    raw,bags=direct_product(h)
    assert solve(raw,bags)[0]==result
    if h==5:assert solve(raw,bags,max_assignments=2)[0]=='UNKNOWN'
raw=build(10,[])
bags=[range(5),range(5,10)]
for i,(u,v) in enumerate(combinations(range(11),2)):
    if u<5<=v<10:raw.zero|=(5 if u+5!=v else 4)<<(4*i)
status,w=solve(raw,bags)
assert status=='SAT' and not apply_word(raw,w)&raw.zero
assert solve(raw,None,max_assignments=0)[0]=='UNKNOWN'
raw.zero|=1
assert solve(raw,bags)[0]=='UNKNOWN'
for n in (1,3,5):
    assert solve(build(n,[]))[0]=='SAT'
print('K5×K4 abstains, K5×K5 UNSAT, mixed pins SAT, limit, padding and internal checks passed')
