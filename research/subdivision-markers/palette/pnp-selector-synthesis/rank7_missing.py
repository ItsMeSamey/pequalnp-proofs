from itertools import combinations
from wedge_checks import direct
from wedge_path import wedge
from frontier import basis
from signature_bounds import bounds
from recognizer import bit_indices
data=[17,23,24,28,35,38,40,47,62,64,74,83,90,92,100,104,109]
cols=[(v>>4,(v>>2)&3) for v in data]
def kernel(rows,dim):
    rows=basis(rows)
    piv={row.bit_length()-1 for row in rows}
    return basis((1<<i)|sum((1<<(row.bit_length()-1)) for row in rows if row>>i&1)
                 for i in range(dim) if i not in piv)
def main():
    W,L=direct(cols)
    r=len(L)
    piv=[u.bit_length()-1 for u in L]
    pairs=list(combinations(range(r),2))
    def proj(z):
        out=0
        for a,b in pairs:
            i,j=sorted((piv[a],piv[b]))
            out|=((z>>(j*(j-1)//2+i))&1)<<(b*(b-1)//2+a)
        return out
    local=basis(proj(z) for z in W)
    _,_,constraints=bounds(cols,L)
    exact=kernel(local,r*(r-1)//2)
    mapped=[]
    for bit in (0,1):
        h=sum(((row>>bit)&1)<<i for i,row in enumerate(data))
        mapped.append(sum(((h&u).bit_count()%2)<<i for i,u in enumerate(L)))
    target=wedge(*mapped)
    print('basis of L indexed masks',','.join(map(str,L)))
    print('actual h1,h2 local masks',mapped,'target in single-conflict annihilator',len(basis(constraints+(target,)))==len(constraints))
    assert not any((target&z).bit_count()%2 for z in local)
    base=constraints
    additions=[]
    for a in (target,)+exact:
        new=basis(base+(a,))
        if len(new)>len(base):
            additions.append(a)
            base=new
    print('independent extra form masks',','.join(map(str,additions)))
    assert len(additions)==14 and base==exact
    return local,constraints,additions
if __name__=='__main__': main()
