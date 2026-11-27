"""Canonical tail-translation keys for projected bijunctive prefix relations.
Scopes use 1-based DIMACS variable IDs; global shift words use bit v-1.
"""
from collections import defaultdict


def parity(x):return x.bit_count() & 1


def translate(table,shift):
    out=0
    while table:
        bit=table & -table
        out |= 1<<((bit.bit_length()-1)^shift)
        table^=bit
    return out


def lift(mask,scope):
    return sum(1<<(v-1) for j,v in enumerate(scope) if mask>>j&1)


def insert(rows,word,rep):
    for p in sorted(rows,reverse=True):
        if word>>p&1:
            a,b=rows[p];word^=a;rep^=b
    if word:rows[word.bit_length()-1]=(word,rep)
    return word,rep


def equations_for_group(scope,table):
    size=1<<len(scope)
    group=[t for t in range(size) if translate(table,t)==table]
    rows={}
    for c in range(1,size):
        if all(not parity(t&c) for t in group):insert(rows,c,0)
    return tuple(lift(v,scope) for v,_ in rows.values())


def tail_equations(clauses,*,fixed=()):
    grouped={}
    for clause in clauses:
        lits=set(clause)
        if 0 in lits:raise ValueError('zero literal')
        if any(-v in lits for v in lits):continue
        scope=tuple(sorted(abs(v) for v in lits))
        if len(scope)>3:raise ValueError('tail scope exceeds three')
        bad=sum((1<<j) for j,v in enumerate(scope) if -v in lits)
        grouped[scope]=grouped.get(scope,(1<<(1<<len(scope)))-1)&~(1<<bad)
    rows={}
    for scope,table in grouped.items():
        for equation in equations_for_group(scope,table):insert(rows,equation,0)
    for v in fixed:
        if v<=0:raise ValueError('invalid frozen name')
        insert(rows,1<<(v-1),0)
    return tuple(a for a,_ in rows.values())


def kernel(n,equations):
    rows={}
    for equation in equations:
        if equation<0 or equation.bit_length()>n:raise ValueError('invalid tail equation')
        insert(rows,equation,0)
    values=[]
    for j in range(n):
        if j in rows:continue
        word=1<<j
        for p in sorted(rows):
            if parity(word&rows[p][0]):word|=1<<p
        values.append(word)
    return tuple(values)


def orbit_key(signature,tail_basis):
    """Return (hashable key, raw word translating to its canonical phase).
    Signature must include all 0/1/2 projections for the same named boundary.
    """
    if signature.get(())==0:return ('empty',),0
    if signature.get(())!=1:raise ValueError('nullary projection required')
    variables=sorted(scope[0] for scope in signature if len(scope)==1)
    expected=1+len(variables)*(len(variables)+1)//2
    if len(signature)!=expected:raise ValueError('incomplete projection signature')
    rows=[]; local=[];phase=0
    for scope,table in sorted(signature.items()):
        if not scope:continue
        if (len(scope)>2 or tuple(sorted(set(scope)))!=scope or
                any(v not in variables or v<=0 for v in scope)):
            raise ValueError('invalid projection scope')
        size=1<<len(scope)
        if not 0<table<1<<size:raise ValueError('invalid nonempty table')
        canonical,delta=min((translate(table,t),t) for t in range(size))
        local.append((scope,canonical))
        for c in equations_for_group(tuple(range(1,len(scope)+1)),canonical):
            phase|=parity(delta&c)<<len(rows)
            rows.append(lift(c,scope))
    images={}
    for raw in tail_basis:
        image=sum(parity(raw&c)<<i for i,c in enumerate(rows))
        insert(images,image,raw)
    shift=0
    for pivot in sorted(images,reverse=True):
        if phase>>pivot&1:
            v,w=images[pivot];phase^=v;shift^=w
    return (tuple(local),phase),shift


def translator(left,right,tail_basis):
    a,x=orbit_key(left,tail_basis);b,y=orbit_key(right,tail_basis)
    return x^y if a==b else None


def from_forbidden(front,forbidden):
    from itertools import combinations
    sig={():1}
    for arity in (1,2):
        for scope in combinations(front,arity):
            table=0
            for y in range(1<<arity):
                clause=tuple(-v if y>>i&1 else v for i,v in enumerate(scope))
                if clause not in forbidden:table|=1<<y
            sig[scope]=table
    return sig


class TailOrbits:
    """Construct one per solve; cache diagram keys only in the current layer."""
    def __init__(self,n):
        self.n=n
        self.layer=None
        self.keys={}
        self.groups=0
        self.key_calls=0

    def key(self,j,front,diagram,banks,selectors):
        if self.layer!=j:
            tail=[]
            for i in range(j+1,len(banks)):
                s=selectors[i-1]
                for val,collection in enumerate(banks[i]):
                    guard=s if val==0 else -s
                    tail.extend((guard,)+tuple(row) for row in collection)
            self.basis=kernel(self.n,tail_equations(tail,fixed=selectors[:j]))
            self.layer=j;self.keys={};self.groups+=1
        if diagram not in self.keys:
            self.keys[diagram]=orbit_key(from_forbidden(front,diagram),self.basis)
            self.key_calls+=1
        return self.keys[diagram]

    def __call__(self,j,front,left,right,banks,selectors):
        a,_=self.key(j,front,left,banks,selectors)
        b,_=self.key(j,front,right,banks,selectors)
        return a==b
