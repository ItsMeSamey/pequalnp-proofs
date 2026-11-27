"""Synchronous scalar product using a certified reachable basis of pure pairs."""
from boolean_value_automata import apply, coordinates, dot, indices, insert, minimize


def tensor_coordinate(uv, pivot):
    a,b=uv
    i,j=pivot
    return ((a>>i)&(b>>j)&1)


def separating_coordinate(terms):
    """Find a nonzero entry of sum u v^T without materializing that matrix."""
    vbasis={}
    rows=[]
    coefficients=[]
    for u,v in terms:
        if insert(vbasis,v,1<<len(rows)):
            coefficients.append(1<<len(rows))
            rows.append(v)
        else:
            coefficients.append(coordinates(vbasis,v))
    sums=[0]*len(rows)
    for (u,_),coeff in zip(terms,coefficients):
        for j in indices(coeff):
            sums[j]^=u
    for col in sums:
        if col:
            i=(col&-col).bit_length()-1
            actual=0
            for u,v in terms:
                if u>>i&1:
                    actual^=v
            if not actual:
                raise AssertionError('inconsistent factor basis')
            return i,(actual&-actual).bit_length()-1
    return None


class PureBasis:
    def __init__(self):
        self.pairs=[]
        self.pivots=[]
        self.interpolants=[]

    def represent_or_extend(self,uv,cap):
        coefficients=0
        for pivot, correction in zip(self.pivots,self.interpolants):
            discrepancy=tensor_coordinate(uv,pivot)
            for i in indices(coefficients):
                discrepancy^=tensor_coordinate(self.pairs[i],pivot)
            if discrepancy:
                coefficients^=correction
        residual=[uv]+[self.pairs[i] for i in indices(coefficients)]
        pivot=separating_coordinate(residual)
        if pivot is None:
            return coefficients
        if len(self.pairs)>=cap:
            raise OverflowError('certified reachable-rank cap exceeded')
        unit=1<<len(self.pairs)
        self.pairs.append(uv)
        self.pivots.append(pivot)
        self.interpolants.append(coefficients^unit)
        return unit


def implicit_product(p,q,*,rank_cap,cell_budget):
    """Returns status complete or skip. Budget counts compact-matrix dense slots."""
    a,start,ps,end=p
    b,other,qs,finish=q
    if len(ps)!=len(qs):
        raise ValueError('different input lengths')
    cost={'candidates':0,'compact_cells':0,'max_reached_rank':0,
          'formal_width':max(x*y for x,y in zip(a,b)),
          'formal_cells':sum(2*a[i]*b[i]*a[i+1]*b[i+1] for i in range(len(ps)))}
    current=PureBasis()
    try:
        initial=current.represent_or_extend((start,other),rank_cap)
        widths=[len(current.pairs)]
        cost['max_reached_rank']=widths[0]
        transitions=[]
        for pl,ql in zip(ps,qs):
            nxt=PureBasis()
            layer=[]
            for pm,qm in zip(pl,ql):
                entries=[]
                for u,v in current.pairs:
                    cost['candidates']+=1
                    entries.append(nxt.represent_or_extend((apply(u,pm),apply(v,qm)),rank_cap))
                    if cost['compact_cells']+2*len(current.pairs)*len(nxt.pairs)>cell_budget:
                        raise OverflowError('compact transition cap exceeded')
                layer.append(tuple(entries))
            cost['compact_cells']+=2*len(current.pairs)*len(nxt.pairs)
            cost['max_reached_rank']=max(cost['max_reached_rank'],len(nxt.pairs))
            transitions.append(tuple(layer))
            widths.append(len(nxt.pairs))
            current=nxt
    except OverflowError as exc:
        return {'status':'skip','reason':str(exc),'cost':cost}
    terminal=sum((dot(u,end)&dot(v,finish))<<i for i,(u,v) in enumerate(current.pairs))
    minimized,word=minimize((widths,initial,transitions,terminal))
    return {'status':'complete','program':minimized,'word':word,'cost':cost}
