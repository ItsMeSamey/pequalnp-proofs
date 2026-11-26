"""Find stabilizer rays in three-dimensional local spans through real CCZ, exactly."""
import itertools as it
import numpy as np
from math import comb

p = 65537
unit = (1,256,p-1,p-256)
def normalize(a):
    e=next(e for e in a if e!=-1)
    return tuple((v-e)%4 if v!=-1 else -1 for v in a)
def stabs():
    out=set()
    for U in range(1,256):
        pts=[x for x in range(8) if U>>x&1]
        h=pts[0]; coords={0:0};basis=[]
        for point in pts:
            v=point^h
            if v not in coords:
                j=len(basis);basis.append(v)
                coords.update({x^v:c^(1<<j) for x,c in list(coords.items())})
        if len(coords)!=len(pts):continue
        k=len(basis); edges=list(it.combinations(range(k),2))
        for ls in it.product(range(4),repeat=k):
            for m in range(1<<len(edges)):
                vec=[-1]*8
                for x,c in coords.items():
                    lin=sum(w for j,w in enumerate(ls) if c>>j&1)
                    quad=sum(2 for j,(a,b) in enumerate(edges) if m>>j&1 and c>>a&1 and c>>b&1)
                    vec[x^h]=(lin+quad)%4
                out.add(tuple(vec))
    return sorted(out)
def orbit_reps(rows):
    ids={r:i for i,r in enumerate(rows)}; maps=[]
    for j in range(3):
        off=1<<j
        maps.append(([x^off for x in range(8)],[2*((x==7)^((x^off)==7)) for x in range(8)]))
        for k in range(3):
            if j!=k:maps.append(([x^((1<<j) if ((x^7)>>k&1) else 0) for x in range(8)],[0]*8))
    perm=[]
    for f,delta in maps:
        perm.append([ids[normalize([-1 if row[f[x]]<0 else (row[f[x]]+delta[x])%4 for x in range(8)])] for row in rows])
    left=set(range(len(rows))); reps=[]
    while left:
        root=min(left);left.remove(root);todo=[root];sz=0
        while todo:
            cur=todo.pop();sz+=1
            for v in perm:
                nxt=v[cur]
                if nxt in left:left.remove(nxt);todo.append(nxt)
        reps.append((root,sz))
    return reps

def pivots(a,mod):
    a=a.copy()%mod;used=[];r=0
    for col in range(a.shape[1]):
        if r==len(a):break
        ix=np.flatnonzero(a[r:,col])
        if not len(ix):continue
        i=r+ix[0]
        a[[r,i]]=a[[i,r]]
        row=a[r]*pow(int(a[r,col]),-1,mod)%mod
        for j in range(r+1,len(a)):a[j]=(a[j]-a[j,col]*row)%mod
        used.append(col);r+=1
    return used

def inv3(m):
    aug=np.concatenate((m.copy(),np.eye(3,dtype=np.int64)),axis=1)
    for c in range(3):
        j=next(k for k in range(c,3) if aug[k,c]%p)
        aug[[j,c]]=aug[[c,j]];aug[c]=aug[c]*pow(int(aug[c,c]),-1,p)%p
        for k in range(3):
            if k!=c:aug[k]=(aug[k]-aug[k,c]*aug[c])%p
    return aug[:,3:]

def main():
    rows=stabs();assert len(rows)==1080
    reps=orbit_reps(rows); print('orbits',reps,flush=True)
    matrix=np.array([[0 if x<0 else unit[x] for x in row] for row in rows],dtype=np.int64)
    g=np.array([1]*7+[p-1]); hits=set(); max_n=0;hist={}
    for a,_ in reps:
        for b in range(len(rows)):
            block=np.array([g,matrix[a],matrix[b]])
            pivot=pivots(block,p)
            if len(pivot)<3:continue
            T=inv3(block[:,pivot])@block%p
            members=tuple(int(i) for i in np.flatnonzero(np.all(matrix[:,pivot]@T%p==matrix,axis=1)))
            max_n=max(max_n,len(members))
            hist[len(members)]=hist.get(len(members),0)+1
            if len(members)>=7:hits.add(members)
    print('max',max_n,'hist',hist,'7+ distinct examined planes',len(hits),flush=True)
    np.save('/tmp/g3_complex_plane_hits.npy',np.array(sorted(hits),dtype=object),allow_pickle=True)
if __name__=='__main__':main()
