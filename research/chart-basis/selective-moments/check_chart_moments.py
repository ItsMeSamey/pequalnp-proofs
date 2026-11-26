"""Exact small-instance verification of pair-union incidence moment spans."""
from itertools import combinations
from pit_chart_scan import scan,insert


def orthogonal(rows,n):
    p={}
    for x in rows:insert(x,p)
    out=[]
    for i in range(n):
        if i in p:continue
        x=1<<i
        for j,row in sorted(p.items()):
            if (x&row).bit_count()%2:x|=1<<j
        out.append(x)
    return out


def run(c,r,ell,u,k):
    features=[j for i in range(k+1) for j in combinations(range(2,len(c)),i)]
    m=len(features)
    cells=[[] for _ in range(8)]
    for X,a,b,g in scan(c,r,0,1,ell,u)[3]:
        vec=sum(1<<j for j,I in enumerate(features) if set(I)<=set(X))
        cells[4*a+2*b+g].append((X,vec))
    constraints=[]
    for i in range(8):
        normals=[]
        for j in range(8):
            if i!=j:
                normals+=orthogonal((v for X,v in cells[i]+cells[j]),m)
        constraints.append(normals)
    neg=[i for i in range(8) if not any(v&1 for v in orthogonal(constraints[i],m))]
    pos=[]
    for i in range(8):
        for j in range(8):
            if i==j:continue
            outside=[x for x,v in cells[i]+cells[j] if any((v&w).bit_count()%2 for w in constraints[j])]
            if outside:
                assert all(x in [z for z,_ in cells[i]] for x in outside)
                pos.append(i)
                break
    assert all(not cells[i] for i in neg)
    return cells,neg,pos

if __name__=='__main__':
    for c,r,e,u in [([19,26,20,17,7,5,13,6,21,4],5,205,28),
                     ([13,4,2,5,1,8,14,7,3],4,64,0)]:
        for k in (0,1,2):
            cells,neg,pos=run(c,r,e,u,k)
            if r==5:
                assert all(cells)
                assert all(9 not in x for i in [6,7] for x,_ in cells[i])
                assert all(9 in x for x,_ in cells[1])
                if k: assert 6 in pos and 7 in pos
            print(r,k,neg,pos)
