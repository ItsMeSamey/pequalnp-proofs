"""Two-dimensional gate-level check of the dyadic corner-array extension."""
from itertools import product
from interval_compiler import Circuit, IntervalIndex

def axis_parts(l,r):
    if l==r:
        return [(l,1,True,1)]
    size=1<<(l^r).bit_length()
    start=(l//size)*size
    half=size//2
    return [(start,half,False,start+half-l),(start+half,half,True,r-start-half+1)]

def minimum(c,a,b):
    lt=-c.true
    for x,y in zip(a,b):
        lt=c.gate('or',c.gate('and',-x,y),c.gate('and',c.gate('or',-x,y),lt))
    return tuple(c.mux(lt,x,y) for x,y in zip(a,b))

class Boxes:
    def __init__(self,c,h,w):
        self.c=c
        self.tables={}
        H=1<<(h-1).bit_length()
        W=1<<(w-1).bit_length()
        grid=[[1+i*w+j if i<h and j<w else -c.true for j in range(W)] for i in range(H)]
        rows=[IntervalIndex(c,row) for row in grid]
        cols=[IntervalIndex(c,col) for col in zip(*grid)]
        self.one=rows[0]
        for j in range(H.bit_length()):
            for k in range(W.bit_length()):
                hh,ww=1<<j,1<<k
                horizontal=ww>=hh
                for i in range(0,H,hh):
                    for l in range(0,W,ww):
                        for top,left in product((True,False),repeat=2):
                            before=None
                            small=hh if horizontal else ww
                            for t in range(small):
                                if horizontal:
                                    z=i+(t if top else hh-1-t)
                                    extent=rows[z].nodes[l,ww][0 if left else 1]
                                else:
                                    z=l+(t if left else ww-1-t)
                                    extent=cols[z].nodes[i,hh][0 if top else 1]
                                before=extent if before is None else minimum(c,before,extent)
                                self.tables[i,hh,top,l,ww,left,t+1]=self.one.thresholds(before)

    def tests(self,y1,y2,x1,x2):
        ans=[]
        for i,h,top,hi in axis_parts(y1,y2):
            for j,w,left,wi in axis_parts(x1,x2):
                small,long=(hi,wi) if w>=h else (wi,hi)
                table=self.tables[i,h,top,j,w,left,small]
                ans.append(self.one.covers(table,long))
        return ans

if __name__=='__main__':
    cases=0
    for h,w in [(1,2),(2,3),(3,2),(3,3)]:
        circuit=Circuit(h*w)
        index=Boxes(circuit,h,w)
        all_boxes=[(i,j,k,l) for i in range(h) for j in range(i,h)
                   for k in range(w) for l in range(k,w)]
        selectors=[index.tests(*b) for b in all_boxes]
        for x in product((False,True),repeat=h*w):
            vals=circuit.extend(x)
            for (i,j,k,l),parts in zip(all_boxes,selectors):
                zero=all(any(all(vals[abs(z)]==(z>0) for z in term)
                             for term in choices) for choices in parts)
                assert zero==(not any(x[a*w+b] for a in range(i,j+1) for b in range(k,l+1)))
                cases+=1
    print(f'{cases} full-grid Boolean rectangle queries agree with gate-generated corner tables.')
