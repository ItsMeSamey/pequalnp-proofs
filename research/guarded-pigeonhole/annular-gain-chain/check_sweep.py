from check import test_path
from sweep import ordered_sweep
import random
rng=random.Random(1421)
yes=0;count=0
for n,rep in [(1,35),(2,25),(3,5)]:
 for case in range(rep):
    stars=[];cycles=[]
    for i in range(n):
        a,b=2*i,2*i+1
        inside=2*n+i;outside=inside+1
        # Lens cycles are all odd. Their third incidences may run directly to an adjacent separator disk.
        x=rng.choice([inside]+([2*i-2,2*i-1] if i else []))
        y=rng.choice([outside]+([2*i+2,2*i+3] if i+1<n else []))
        stars.extend([{a:0,b:0,x:0},{a:0,b:1,y:0}]);cycles.append(((2*i,2*i+1),(a,b)))
    # Single bridge star in each annular region, with either boundary disk as a possible contact.
    for i in range(n+1):
        choices=([2*(i-1),2*(i-1)+1] if i else [])+([2*i,2*i+1] if i<n else [])
        ds=[2*n+i]+rng.sample(choices,min(len(choices),rng.randrange(1,3)))
        stars.append(dict.fromkeys(ds,0))
    s,t=rng.sample(range(3*n+1),2)
    actual=ordered_sweep(stars,s,t,cycles)
    assert actual==test_path(stars,s,t)
    count+=1;yes+=actual
print('separator comparisons',count,'YES',yes)
for n in range(1,5):
    base=[];cycles=[]
    for i in range(n):
        base+= [{2*i:0,2*i+1:0,2*n+i:0},{2*i:0,2*i+1:1,2*n+i+1:0}]
        cycles.append(((2*i,2*i+1),(2*i,2*i+1)))
    for mask in range(1<<n):
        stars=base+[{2*i:0,2*n+i+1:0} for i in range(n) if mask>>i&1]
        actual=ordered_sweep(stars,2*n,3*n,cycles)
        assert actual==test_path(stars,2*n,3*n)==(mask==(1<<n)-1)
print('30 nested gate controls, 4 YES and 26 NO')
