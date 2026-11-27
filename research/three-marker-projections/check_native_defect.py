from itertools import product
from random import Random
from fractions import Fraction
import native_net_defect as net
import native_paired_rows as pair
from check_native_cut_dp import joins

def det(rows):
    a=[list(v) for v in rows];v=1;n=len(a)
    for i in range(n):
        j=next((j for j in range(i,n) if a[j][i]),None)
        if j is None:return 0
        if j!=i:a[j],a[i]=a[i],a[j];v=-v
        p=a[i][i];v*=p
        for j in range(i+1,n):
            q=Fraction(a[j][i],p)
            if q:
                for k in range(i,n):a[j][k]-=q*a[i][k]
    return v

def run():
    rng=Random(7117);count=0
    for n in (1,2,3,4,5):
        for _ in range(12 if n<4 else 3):
            p=list(range(3*n));rng.shuffle(p)
            r,s=rng.sample(range(3*n),2)
            m=[rng.choice([(0,1),(0,1,2),(1,2),(1,)]) for _ in range(n)]
            o=pair.prepare(p,m,r,s)
            total=sum(abs(det([v for _,ab in word for v in ab])) for word in product(*o))
            assert net.evaluate(o,{})==total,(p,m,r,s,total,net.evaluate(o,{}))
            for solver in (pair.solve,net.solve):
                w=solver(p,m,r,s)
                assert (w is not None)==bool(total) and (w is None or joins(p,w,r,s))
            count+=1
    print(count,'exact absolute cofactor sums and two original-mask witness algorithms passed')
if __name__=='__main__':run()
