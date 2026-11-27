"""Choose a certified search bound across supplied physical-selector budgets."""
from functools import reduce
from itertools import combinations
from math import comb
from operator import xor
from common_period import difference_level
from determinant_degree import height_anf, parity_toggle
from fixed_height import recognize, prior
from recognizer import tag_at

def minors(columns,cert):
    vectors=[[{0},set()],[set(),{0}]]
    vectors.extend(height_anf(columns,cert,history) for _,history in cert.anchors)
    family=set()
    for i,left in enumerate(vectors):
        for right in vectors[:i]:
            terms=set()
            for a,b in ((left[0],right[1]),(left[1],right[0])):
                for x in a:
                    for y in b:
                        parity_toggle(terms,x|y)
            if terms: family.add(frozenset(terms))
    return family

def filtration(family,bits):
    """Yield (degree bound on each coset, codimension)."""
    family=tuple(frozenset(poly) for poly in family)
    degree=max((m.bit_count() for f in family for m in f),default=0)
    basis=[1<<i for i in range(bits)]
    yield degree,0
    for level in reversed(range(degree)):
        rows,labels,kernel={},{},[]
        for shift in basis:
            residual=0
            for index,poly in enumerate(family):
                for term in difference_level(poly,shift,level):
                    key=(index,term)
                    residual ^= 1<<labels.setdefault(key,len(labels))
            while residual:
                lead=residual.bit_length()-1
                if lead not in rows:
                    rows[lead]=(residual,shift)
                    break
                old,original=rows[lead]
                residual ^= old
                shift ^= original
            if not residual: kernel.append(shift)
        basis=kernel
        yield level,bits-len(basis)

from dataclasses import dataclass
@dataclass(frozen=True)
class Plan:
    mode: str
    cap: int
    odd_limit: int
    work_bound: int
    budget: tuple
    deficit: int
    slice_degree: int
    codimension: int

def plan_search(columns,dimension,budgets):
    columns=tuple(columns)
    bits=2*dimension
    best=None
    for s,h in budgets:
        cert=recognize(columns,dimension,s,h)
        t=dimension-len(cert.anchors)
        if best is None:
            best=Plan('cube',0,1,1<<bits,(s,h),t,0,0)
        for j,c in filtration(minors(columns,cert),bits):
            cap=min(bits,2*(t+2)+c)
            length=2*(j//2)+1
            field_bits=(bits<<(cap+1)).bit_length()
            count=1<<(2*field_bits)
            if count>=best.work_bound: continue
            bound=count
            for size in range(1,min(length,count)+1,2):
                bound+=comb(count,size)
                if bound>=best.work_bound: break
            if bound<best.work_bound:
                best=Plan('seed',cap,length,bound,(s,h),t,j,c)
    if best is None: raise ValueError('supply at least one selector budget')
    return best

def solve(columns,dimension,budgets):
    columns=tuple(columns)
    plan=plan_search(columns,dimension,budgets)
    def candidates():
        if plan.mode=='cube':
            yield from range(1<<(2*dimension))
        else:
            points=prior['seeds'](2*dimension,plan.cap)
            for length in range(1,plan.odd_limit+1,2):
                for group in combinations(points,length):
                    yield reduce(xor,group)
    for chart in candidates():
        physical,private,indices={},{},[]
        for i,(k,b,h) in enumerate(columns):
            if tag_at(chart,k,dimension)!=b: continue
            prior['add'](private,k)
            if prior['add'](physical,(k<<2)|h): indices.append(i)
        if len(physical)-len(private)==2: return plan,indices
    return plan,None
