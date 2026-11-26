"""Direct socket and chord-table audit, plus the complete normalized scalar search."""
from itertools import permutations, product

WORD = (0,2,3,1,2,0,3,1,2,3,0,1)
EXPECT = (1,0,0,1,0,0,1,1,0,0,1,1,1,0,1,1)
SOCKETS = [[i for i,g in enumerate(WORD) if g==v] for v in range(4)]

def socket(mask):
    move=list(range(12))
    for v,a in enumerate(SOCKETS):
        if mask>>v&1:
            for j,t in enumerate(a):move[t]=a[(j-1)%3]
    seen=set();t=0
    while t not in seen:
        seen.add(t);t=(move[t]+1)%12
    return int(len(seen)==12)

def paired(mask):
    # Two independent occurrence positions at the gate's first visit.
    chords=[]
    for v,(a,b,c) in enumerate(SOCKETS):
        if mask>>v&1:chords.extend(((2*a,2*c),(2*a+1,2*b)))
    def rec(L):
        if not L:return 1
        a,b=L[0];out=0
        for j,(u,v) in enumerate(L[1:],1):
            if (a<u<b)!=(a<v<b):out ^= rec(L[1:j]+L[j+1:])
        return out
    return rec(chords)

# GF(4), w^2=w+1. The proof forces all normalized entries into this subfield.
def mul(a,b):
    z=(a if b&1 else 0)^((a<<1) if b&2 else 0)
    return z^7 if z&4 else z

def pm(M,mask):
    I=[i for i in range(4) if mask>>i&1]
    val=0
    for pi in permutations(I):
        p=1
        for i,j in zip(I,pi):p=mul(p,M[i][j])
        val^=p
    return val

def main():
    assert tuple(map(socket,range(16)))==EXPECT
    assert tuple(map(paired,range(16)))==EXPECT
    attainable=[]
    for a,b,t in product((0,1),(0,1),(2,3)):
        M=[[0,1,a,b],[1,0,1,1],[1^a,1,0,t],[1^b,1,t^1,0]]
        if all(pm(M,m)==EXPECT[m] for m in range(15)):
            attainable.append(pm(M,15))
    assert attainable==[0]*4
    print('16 physical socket permutations and paired Pfaffians agree; all four normalized candidates force zero full determinant.')
if __name__=='__main__':main()
