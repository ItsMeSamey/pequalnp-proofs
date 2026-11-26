"""Check bounded-port composition against complete enumeration after gluing."""
from itertools import product
from random import Random
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/"unseeded-root-states"))
from solve import canonical, image, eliminate, solve

def points(U):
    return tuple(image(U,i) for i in range(1<<len(U)))

def subspaces(s):
    out={()}
    for v in range(1,1<<s):
        out.update(canonical(L+(v,)) for L in tuple(out))
    return sorted(out)

def rank(cols):
    return len(canonical(cols))

def reduce_mod(v,piv):
    for i,(row,_) in sorted(piv.items(),reverse=True):
        if (v>>i)&1:
            v^=row
    return v

class Piece:
    def __init__(self,d,cols,tags,ports):
        self.d,self.cols,self.tags,self.ports=d,tuple(cols),tuple(tags),ports

def assignments(cols,tags):
    for color in product(range(4),repeat=len(cols)):
        zeros=tuple(c for c,v in zip(cols,color) if v==0)
        if rank(zeros)!=len(zeros):
            continue
        f=g=t=0
        for v,a,(b,c) in zip(color,cols,tags):
            if v&1:
                f^=a
                t^=b
            if v&2:
                g^=a
                t^=c
        yield f,g,t,zeros,color

def flatten(pieces):
    offsets=[]
    total=0
    for p in pieces:
        offsets.append(total)
        total+=p.d
    relations=[]
    for i,p in enumerate(pieces):
        for j,U in p.ports.items():
            if j<i:
                relations.extend((u<<offsets[i])^(v<<offsets[j])
                                 for u,v in zip(U,pieces[j].ports[i]))
    piv,_=eliminate(relations)
    cols=[reduce_mod(c<<offsets[i],piv) for i,p in enumerate(pieces) for c in p.cols]
    return cols,[tag for p in pieces for tag in p.tags]

def portfolio(pieces):
    # Numbering increases along every root-to-leaf path.
    tables={}
    for i in reversed(range(len(pieces))):
        p=pieces[i]
        parents=[j for j in p.ports if j<i]
        assert len(parents)==(i!=0)
        U=p.ports[parents[0]] if parents else ()
        coords=points(U)
        children=[j for j in p.ports if j>i]
        table={}
        for row in product(*(set(tables[j].values()) for j in children)):
            need_f=need_g=ct=0
            probes=[]
            saved=[]
            for j,(f,g,t,L,witness) in zip(children,row):
                port=p.ports[j]
                need_f^=image(port,f)
                need_g^=image(port,g)
                ct^=t
                probes.extend(image(port,x) for x in L)
                saved+=list(witness)
            for a,b,t,zero,colors in assignments(p.cols,p.tags):
                f=a^need_f
                g=b^need_g
                if f not in coords or g not in coords:
                    continue
                joint=tuple(probes)+zero
                if rank(joint)!=len(joint):
                    continue
                L=canonical(x for x,u in enumerate(coords) if solve(joint,u) is not None)
                f,g=coords.index(f),coords.index(g)
                witness=tuple(saved+[(i,colors)])
                for K in subspaces(len(U)):
                    if rank(L+K)==len(L)+len(K):
                        table.setdefault((f,g,t^ct,K),(f,g,t^ct,L,witness))
        tables[i]=table
    return {t:w for (_,_,t,_),(_,_,_,_,w) in tables[0].items()}

def verify(pieces):
    cols,tags=flatten(pieces)
    good={t for f,g,t,_,_ in assignments(cols,tags) if f==g==0}
    got=portfolio(pieces)
    assert set(got)==good
    for t,w in got.items():
        colors=tuple(x for _,chunk in sorted(w) for x in chunk)
        zeros=[v for v,c in zip(cols,colors) if not c]
        fbits=sum(int(bool(c&1))<<j for j,c in enumerate(colors))
        gbits=sum(int(bool(c&2))<<j for j,c in enumerate(colors))
        assert rank(zeros)==len(zeros)
        assert image(cols,fbits)==image(cols,gbits)==0
        assert (image([a for a,b in tags],fbits)^image([b for a,b in tags],gbits))==t
    return len(good)

def main():
    rng=Random(3199)
    targets=0
    for rep in range(100):
        n=rng.randint(2,4)
        neighbors=[{} for _ in range(n)]
        d=[rng.randrange(2,5) for _ in range(n)]
        for j in range(1,n):
            i=rng.randrange(j)
            s=rng.randint(1,2)
            for q,v in ((i,j),(j,i)):
                U=()
                while len(U)<s:
                    z=rng.randrange(1,1<<d[q])
                    if solve(U,z) is None:
                        U=U+(z,)
                neighbors[q][v]=U
        pieces=[]
        for i in range(n):
            cols=[rng.randrange(1<<d[i]) for _ in range(rng.randrange(3))]
            tags=[(rng.randrange(8),rng.randrange(8)) for _ in cols]
            pieces.append(Piece(d[i],cols,tags,neighbors[i]))
        targets+=verify(pieces)
    # The three child port vectors in the host have a joint dependence.
    star=[Piece(2,[3],[(0,0)],{1:(1,),2:(2,),3:(3,)}),
          Piece(1,[1],[(1,2)],{0:(1,)}),Piece(1,[1],[(2,4)],{0:(1,)}),
          Piece(1,[1],[(3,5)],{0:(1,)})]
    targets+=verify(star)
    print('101 tree pushouts, recovered targets',targets)

if __name__=='__main__':
    main()
