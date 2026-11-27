"""Exact intersection on supplied (order,(widths,initial,layers,final)) GF2 programs."""
from itertools import combinations, product
from math import prod


class Exhausted(Exception):
    pass


class Meter:
    def __init__(self, limit):
        self.limit, self.work = limit, 0

    def add(self, cost=1):
        if cost > self.limit-self.work:
            raise Exhausted
        self.work += cost


def bits(word):
    while word:
        low=word & -word
        yield low.bit_length()-1
        word ^= low


def move(row, matrix, meter):
    result=0
    for i in bits(row):
        meter.add()
        result ^= matrix[i]
    return result


def tensor(rows,widths,meter):
    out=1
    for row,w in zip(rows,widths):
        updated=0
        for i in bits(out):
            meter.add()
            updated |= row << (i*w)
        out=updated
    return out


def search(factor, mode, fixed, meter, cap):
    order,(width,start,layers,end)=factor
    arity={"one":0,"meet":2,"majority":3}[mode]
    count=arity+1
    vocab=list(product((0,1),repeat=max(1,arity)))
    widths=lambda i: [width[i]]*arity+[width[i]+int(bool(arity))]
    if any(prod(widths(i))>cap for i in range(len(width))):
        raise Exhausted
    initial=([start]*arity+[start | ((1<<width[0]) if arity else 0)])
    states=[(initial,(0,)*max(1,arity))]
    for j,raw in enumerate(order):
        basis={}
        nxt=[]
        for rows,words in states:
            for tup in vocab:
                meter.add()
                if not arity and raw in fixed and fixed[raw]!=tup[0]:
                    continue
                vals=tup+(int(sum(tup)>=2),) if arity else tup
                mapped=[]
                for i in range(count):
                    row=rows[i]
                    if arity and i==arity:
                        row &= (1<<width[j])-1
                    mapped.append(move(row,layers[j][vals[i]],meter))
                if arity and rows[-1]>>width[j]:
                    mapped[-1] |= 1<<width[j+1]
                vec=tensor(mapped,widths(j+1),meter)
                while vec:
                    meter.add()
                    pivot=vec.bit_length()-1
                    if pivot not in basis:
                        basis[pivot]=vec
                        nxt.append((mapped,tuple(x|(b<<raw) for x,b in zip(words,tup))))
                        break
                    vec ^= basis[pivot]
        states=nxt
        if not states:
            return None
    for rows,words in states:
        if all(((x & (end|((1<<width[-1]) if arity and i==arity else 0))).bit_count()&1)
               for i,x in enumerate(rows)):
            return words
    return None


def value(factor,x,meter):
    order,(_,row,layers,end)=factor
    for i,raw in enumerate(order):
        row=move(row,layers[i][(x>>raw)&1],meter)
    return (row&end).bit_count()&1


def solve(n,factors,*,mode="meet",pins=None,budget=10000000,width_cap=4096):
    """skip on budget, tensor width, or a locally refuted closure promise."""
    factors=tuple(factors)
    meter=Meter(budget)
    pins={} if pins is None else dict(pins)
    def finish(status,**kwargs):
        return dict(status=status,work=meter.work,**kwargs)
    if mode not in ("meet","majority") or n<0 or any(not 0<=j<n or b not in (0,1) for j,b in pins.items()):
        raise ValueError("invalid mode, arity, or raw pins")
    try:
        for idx,f in enumerate(factors):
            order,(w,s,l,e)=f
            meter.add(n+len(w))
            if sorted(order)!=list(range(n)) or len(w)!=n+1 or len(l)!=n or min(w)<1:
                raise ValueError("invalid program layout")
            if s<0 or e<0 or s.bit_length()>w[0] or e.bit_length()>w[-1]:
                raise ValueError("invalid boundary vector")
            for j,pair in enumerate(l):
                if len(pair)!=2: raise ValueError("invalid layer")
                for mat in pair:
                    meter.add(len(mat))
                    if len(mat)!=w[j] or any(x<0 or x.bit_length()>w[j+1] for x in mat):
                        raise ValueError("invalid binary matrix")
            bad=search(f,mode,{},meter,width_cap)
            if bad is not None:
                return finish("skip",reason="closure",factor=idx,counterexample=bad)
        def possible(f,ass):
            return search(f,"one",ass,meter,width_cap) is not None
        if mode=="meet":
            word=sum(v<<j for j,v in pins.items())
            while True:
                old=word
                for f in factors:
                    ass=pins|{j:1 for j in bits(word)}
                    if not possible(f,ass): return finish("unsat")
                    for j in range(n):
                        if j not in ass and not possible(f,ass|{j:0}):
                            word |= 1<<j
                if old==word: break
        else:
            clauses=[(2*j+v,) for j,v in pins.items()]
            for f in factors:
                if not possible(f,{}): return finish("unsat")
                for size in (1,2):
                    for indices in combinations(range(n),size):
                        for vals in product((0,1),repeat=size):
                            if not possible(f,dict(zip(indices,vals))):
                                clauses.append(tuple(2*i+1-v for i,v in zip(indices,vals)))
            meter.add(n+4*len(clauses))
            word=two_sat(n,clauses)
            if word is None: return finish("unsat")
        if not all(value(f,word,meter) for f in factors) or any((word>>i)&1!=v for i,v in pins.items()):
            raise RuntimeError("original weighted witness replay failed")
        return finish("sat",witness=word)
    except Exhausted:
        return finish("skip",reason="resource cap")


# Binary implication graph solver reused from satbridge/marker-elim/solver.py.
def two_sat(n, clauses):
    # Literal 2*i+v means coordinate i equals v.
    graph = [[] for _ in range(2*n)]
    reverse = [[] for _ in graph]
    for clause in clauses:
        if not clause:
            return None
        a, b = clause[0], clause[-1]
        for u, v in ((a ^ 1, b), (b ^ 1, a)):
            graph[u].append(v)
            reverse[v].append(u)
    seen, order = set(), []
    for root in range(2*n):
        if root in seen:
            continue
        stack = [(root, False)]
        while stack:
            u, done = stack.pop()
            if done:
                order.append(u)
            elif u not in seen:
                seen.add(u)
                stack.append((u, True))
                stack.extend((v, False) for v in graph[u] if v not in seen)
    component = {}
    for label, root in enumerate(reversed(order)):
        if root in component:
            continue
        stack = [root]
        component[root] = label
        while stack:
            u = stack.pop()
            for v in reverse[u]:
                if v not in component:
                    component[v] = label
                    stack.append(v)
    result = 0
    for i in range(n):
        a, b = component[2*i], component[2*i + 1]
        if a == b:
            return None
        result |= int(b > a) << i
    return result
