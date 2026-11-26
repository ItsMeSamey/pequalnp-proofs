"""Exact partial-column feasibility. -1 means zero; 0..3 are phase exponents."""
from itertools import combinations,product

def feasible4(mat,b):
    rows=[list(a)+[v] for a,v in zip(mat,b)]
    if not rows:return True
    cols=list(range(len(mat[0])))
    while True:
        p=next(((i,j) for i,r in enumerate(rows) for j in cols if r[j]&1),None)
        if p is None:break
        i,j=p
        pivot=rows.pop(i)
        pivot=[(x*pivot[j])%4 for x in pivot]
        rows=[[(v-r[j]*u)%4 for v,u in zip(r,pivot)] for r in rows]
        cols.remove(j)
    if any(r[-1]&1 for r in rows):return False
    rows=[[v//2 for v in r] for r in rows]
    for j in cols:
        p=next((i for i,r in enumerate(rows) if r[j]),None)
        if p is None:continue
        pivot=rows.pop(p)
        rows=[[a^b for a,b in zip(r,pivot)] if r[j] else r for r in rows]
    return not any(r[-1] for r in rows)

def feasible(n,partial):
    nz=[v for v,a in partial.items() if a>=0]
    if not nz:return True
    origin=nz[0]
    basis={}
    def remainder(word):
        for pivot in sorted(basis,reverse=True):
            if word>>pivot&1:
                word^=basis[pivot]
        return word
    for v in nz:
        word=remainder(v^origin)
        if word:
            basis[word.bit_length()-1]=word
    if any(a==-1 and remainder(v^origin)==0 for v,a in partial.items()):
        return False
    mat=[]
    for v in nz:
        bits=[v>>j&1 for j in range(n)]
        mat.append([1]+bits+[2*a*b for a,b in combinations(bits,2)])
    return feasible4(mat,[partial[v] for v in nz])

def test():
    atoms={(-1,)*4}
    for mask in range(1,16):
        s=[v for v in range(4) if mask>>v&1]
        if any(a^b^c not in s for a,b,c in product(s,repeat=3)):continue
        for a,b,c,d in product(range(4),range(4),range(4),range(2)):
            atoms.add(tuple((a+b*(x&1)+c*(x>>1)+2*d*int(x==3))%4 if x in s else -1 for x in range(4)))
    for row in product([None,-1,0,1,2,3],repeat=4):
        truth=any(all(a is None or a==v for a,v in zip(row,col)) for col in atoms)
        assert feasible(2,{i:v for i,v in enumerate(row) if v is not None})==truth
    print('1296 partial columns checked')
if __name__=='__main__':test()
