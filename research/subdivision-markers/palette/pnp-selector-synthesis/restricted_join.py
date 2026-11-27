"""Universal join recognizer and polynomial-selector branch witnesses over a binary chart."""
from itertools import product


class RowSpan:
    def __init__(self, forms=()):
        self.rows={}
        for i,form in enumerate(forms):
            self.add(form,1<<i)

    def reduce(self,x):
        evidence=0
        while x:
            j=x.bit_length()-1
            if j not in self.rows:
                break
            form,indices=self.rows[j]
            x ^= form
            evidence ^= indices
        return x,evidence

    def add(self,x,indices):
        x,comb=self.reduce(x)
        if x:
            self.rows[x.bit_length()-1]=(x,comb^indices)
            return True
        return False

    def colors(self,n):
        if self.reduce(1)[0]==0:
            raise ValueError("inconsistent affine system")
        value=1
        for j in sorted(self.rows):
            form,_=self.rows[j]
            value |= ((value&form).bit_count()%2)<<j
        return tuple((value>>(1+2*i))&3 for i in range(n))


def dot(f,x):
    return (f&x).bit_count()%2


def recognize(n,links,first_bits=None):
    """Return (rank, countercoloring or None, selector or None). Links must cross a fixed cut."""
    dense=[]
    sparse=[]
    for i,(u,v,tags) in enumerate(links):
        tags=set(tags)
        if not (0<=u<n and 0<=v<n and u!=v and tags<=set(range(4))):
            raise ValueError("invalid link")
        if not tags:
            continue
        def read(f):
            return (f<<(1+2*u))^(f<<(1+2*v))
        if len(tags)==4:
            return 0,None,lambda colors,i=i:{i}
        if len(tags)==1:
            t=next(iter(tags))
            first = 1 if first_bits is None else first_bits[i]
            if first not in (1,2,3):
                raise ValueError("invalid singleton read functional")
            second = 2 if first == 1 else 1
            sparse.append((i,read(first)^1^dot(first,t),read(second)^1^dot(second,t)))
        else:
            missing=set(range(4))-tags
            for f in (1,2,3):
                values={dot(f,t) for t in missing}
                if len(values)==1:
                    dense.append((i,read(f)^values.pop()))
    dforms=[form for _,form in dense]
    dense_span=RowSpan(dforms)
    fail,_=dense_span.reduce(1)
    reads=[]
    if fail:
        rank_span=RowSpan([1,*dforms])
        for _,a,_ in sparse:
            if rank_span.add(a,0):
                reads.append(a)
    branches={}
    for syndrome in product(range(2),repeat=len(reads)):
        fiber=[v^b for v,b in zip(reads,syndrome)]
        df=RowSpan([*dforms,*fiber])
        substitutions=[]
        linear=[]
        for _,a,b in sparse:
            if not fail:
                eps,comb=0,0
            else:
                residual,comb=df.reduce(a)
                eps=int(bool(residual))
                residual,comb=df.reduce(a^eps)
                assert residual==0
            substitutions.append(comb&((1<<len(dense))-1))
            linear.append(b if eps else 0)
        all_forms=RowSpan([*dforms,*linear,*fiber])
        residual,proof=all_forms.reduce(1)
        if residual:
            return len(reads),all_forms.colors(n),None
        branches[syndrome]=(proof,substitutions)

    def select(colors):
        x=1
        for i,t in enumerate(colors):
            x |= t<<(1+2*i)
        proof,substitutions=branches[tuple(dot(a,x) for a in reads)]
        chosen=set()
        factors=proof&((1<<len(dense))-1)
        for j,(site,a,b) in enumerate(sparse):
            if proof>>(len(dense)+j)&1 and dot(b,x):
                factors ^= substitutions[j]
                if dot(a,x):
                    chosen.add(site)
        for j,(site,d) in enumerate(dense):
            if factors>>j&1 and dot(d,x):
                chosen.symmetric_difference_update((site,))
        return chosen
    return len(reads),None,select
