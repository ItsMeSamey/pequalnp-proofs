"""Explicit old-to-new permutation images for signed-integer 3-CNF and orbit witnesses."""
from dataclasses import dataclass
from itertools import combinations

@dataclass
class Orbit:
    rotation: tuple
    flip: tuple
    start: int
    zero: int
    @property
    def dimension(self):
        return len(self.rotation)

def validate(n,clauses):
    if type(n)!=int or n<0:
        raise ValueError("nonnegative number of variables required")
    cs=[tuple(c) for c in clauses]
    if any(len(c)>3 or any(type(l)!=int or not 1<=abs(l)<=n for l in c) for c in cs):
        raise ValueError("clauses must have at most three in-range signed literals")
    return cs

def labels(n):
    return [(scope,pat) for k in range(1,min(3,n)+1)
            for scope in combinations(range(n),k) for pat in range(1<<k)]

def state(n,x):
    if type(x)!=int or not 0<=x<1<<n:
        raise ValueError("invalid assignment")
    z=0
    for j,(scope,pat) in enumerate(labels(n)):
        if all((x>>v&1)==(pat>>k&1) for k,v in enumerate(scope)):z|=1<<j
    return z

def encode(n,clauses):
    clauses=validate(n,clauses)
    # A pinned extra constant 1-coordinate represents an explicit empty clause.
    lab=labels(n);index={pair:j for j,pair in enumerate(lab)};D=len(lab)
    rot=[];flip=[];zero=0
    for scope,pat in lab:
        shifted=sorted(((v+1)%n,pat>>k&1) for k,v in enumerate(scope))
        rot.append(index[tuple(v for v,_ in shifted),sum(b<<k for k,(_,b) in enumerate(shifted))])
        flip.append(index[scope,pat^(1 if scope[0]==0 else 0)])
    empty=any(not c for c in clauses)
    if empty:rot.append(D);flip.append(D);zero=1<<D
    for c in clauses:
        if not c or any(-l in c for l in c):continue
        scope=tuple(sorted({abs(l)-1 for l in c}))
        pat=sum(int(-v-1 in c)<<j for j,v in enumerate(scope))
        zero|=1<<index[scope,pat]
    return Orbit(tuple(rot),tuple(flip),state(n,0)|(empty<<D),zero)

def move(p,x):
    z=0
    while x:
        b=x&-x;x-=b
        z|=1<<p[b.bit_length()-1]
    return z

def apply_word(instance,word):
    v=instance.start
    for step in word:
        if step not in ('r','f'):raise ValueError("unknown generator")
        v=move(instance.rotation if step=='r' else instance.flip,v)
    return v

def encode_witness(n,clauses,x):
    instance=encode(n,clauses)
    state(n,x)  # Validate the assignment before building the word.
    # After n rotate steps the first flip contributes at coordinate n-1,
    # the last flip contributes at 0.
    word=[]
    for j in reversed(range(n)):
        word.append('r')
        if x>>j&1:word.append('f')
    v=apply_word(instance,word)
    if v&instance.zero:raise ValueError("assignment fails source formula")
    assert v==state(n,x)
    return ''.join(word)

def decode_witness(n,clauses,word):
    clauses=validate(n,clauses);instance=encode(n,clauses)
    v=apply_word(instance,word)
    if v&instance.zero:raise ValueError("word misses the required subcube")
    x=sum(((v>>(2*i+1))&1)<<i for i in range(n))
    if v!=state(n,x) or not all(any((x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses):
        raise AssertionError("physical orbit failed original replay")
    return x

@dataclass
class RawReduction:
    original_n: int
    active: tuple
    clauses: tuple
    orbit: Orbit

    def word_for_true_indices(self,indices):
        names=set(indices)
        if any(type(j)!=int or not 1<=j<=self.original_n for j in names):
            raise ValueError("invalid original true variable")
        x=sum(int(j in names)<<i for i,j in enumerate(self.active))
        return encode_witness(len(self.active),self.clauses,x)

    def true_indices_for_word(self,word):
        x=decode_witness(len(self.active),self.clauses,word)
        return {j for i,j in enumerate(self.active) if x>>i&1}

def reduce_raw(n,clauses):
    """Preserve active names; omitted variables are free and default false on lift."""
    clauses=validate(n,clauses)
    active=tuple(sorted({abs(l) for c in clauses for l in c}))
    to_new={j:i+1 for i,j in enumerate(active)}
    local=tuple(tuple(to_new[abs(l)] if l>0 else -to_new[-l] for l in c) for c in clauses)
    return RawReduction(n,active,local,encode(len(active),local))
