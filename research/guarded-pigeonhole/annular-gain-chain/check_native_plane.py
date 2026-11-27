"""Compare directed smoothing orbits with disk and germ components per mask."""
from random import Random

def cycles(p):
    label=[-1]*len(p)
    count=0
    for start in range(len(p)):
        if label[start]>=0:continue
        i=start
        while label[i]<0:
            label[i]=count;i=p[i]
        count+=1
    return label,count

def audit(n,wire):
    rot=lambda d,k: 6*(d//6)+(d+k)%6
    face,fc=cycles([rot(w,1) for w in wire])
    # A disconnected rotation system with Euler characteristic 2 could
    # comprise a sphere and a torus. Explicitly restrict to connected inputs.
    reached={0}
    while True:
        grown=reached|{wire[d]//6 for d in range(6*n) if d//6 in reached}
        if grown==reached:break
        reached=grown
    if len(reached)!=n or fc!=2+2*n:return 0
    count=0
    for mask in range(1<<n):
        parent=list(range(fc))
        def find(v):
            while v!=parent[v]:v=parent[v]
            return v
        for v in range(n):
            # Turn +1 at incoming (odd) flags when inactive: this follows
            # the face successor rot(wire(.),+1) on outgoing even flags.
            parity=0 if mask>>v&1 else 1
            corners=[face[6*v+parity+2*i] for i in range(3)]
            for c in corners[1:]:parent[find(c)]=find(corners[0])
        model,_=cycles([rot(wire[2*i],-1 if mask>>(wire[2*i]//6)&1 else 1)//2 for i in range(3*n)])
        classes={}
        inv={}
        for i in range(3*n):
            boundary=(find(face[2*i]),find(face[wire[2*i]]))
            if boundary in classes and classes[boundary]!=model[i]:raise AssertionError('duplicate boundary')
            if model[i] in inv and inv[model[i]]!=boundary:raise AssertionError('split boundary')
            classes[boundary]=model[i];inv[model[i]]=boundary
        count+=1
    return count

if __name__=='__main__':
    r=Random(202710)
    counts=[0]*5;settings=0
    for n in range(1,5):
        for _ in range(10000):
            targets=list(range(1,6*n,2));r.shuffle(targets)
            w=[0]*(6*n)
            for i,d in enumerate(targets):w[2*i]=d;w[d]=2*i
            val=audit(n,w)
            if val:counts[n]+=1;settings+=val
            if counts[n]>=60:break
    print(counts[1:],'connected sphere rotations;',settings,'full orbit partitions verified')
