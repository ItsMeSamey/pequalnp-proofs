"""Private normal-space projection and lifting for explicit forbidden tuple lists."""
from collections import defaultdict
from dataclasses import dataclass
from affine_cell_energy import dot, solve
from affine_union_cache import canonical
from affine_cover_solver import insert
from clause_rank_drop import _combination, _image


def values(normals, word):
    return sum(dot(a,word) << i for i,a in enumerate(normals))


def row_basis(n, rows):
    return tuple(a for a,_ in canonical(n,((a,0) for a in rows)))


def scope_split(n, scope, exterior):
    """The input scope is an ordered canonical RREF basis."""
    annihilator=solve(n,((a,0) for a in exterior))[1]
    coordinates=solve(len(scope),((values(scope,z),0) for z in annihilator))[1]
    shared=row_basis(n,(_combination(scope,c) for c in coordinates))
    basis={}
    for a in shared:
        insert(a,0,basis)
    private=[]
    for a in scope:
        before=len(basis)
        insert(a,0,basis)
        if len(basis)>before:
            private.append(a)
    pivots=[a.bit_length()-1 for a in scope]
    def in_scope(a):
        return sum(((a>>k)&1)<<j for j,k in enumerate(pivots))
    return shared,tuple(private),tuple(map(in_scope,shared)),tuple(map(in_scope,private))


@dataclass
class Step:
    exterior: tuple
    shared: tuple
    private: tuple
    excluded: dict


@dataclass
class Reduction:
    n: int
    groups: dict
    steps: list
    impossible: bool = False

    def lift(self, word):
        if self.impossible:
            raise ValueError("inconsistent projection")
        if type(word) is not int or not 0 <= word < 1 << self.n:
            raise ValueError("invalid residual seed")
        if any(values(scope,word) in denied for scope,denied in self.groups.items()):
            raise ValueError("seed violates the residual")
        for step in reversed(self.steps):
            excluded=step.excluded.get(values(step.shared,word),())
            code=0
            while code in excluded:
                code+=1
            if code.bit_length()>len(step.private):
                raise AssertionError("full fiber survived elimination")
            rows=[(a,dot(a,word)) for a in step.exterior]
            rows.extend((a,(code>>j)&1) for j,a in enumerate(step.private))
            word=solve(self.n,rows)[0]
        return word


def reduce_flats(n, flats):
    """Flats are lists of affine equations; the task is to avoid every flat."""
    if type(n) is not int or n<0:
        raise ValueError("invalid dimension")
    groups=defaultdict(set)
    for flat in flats:
        rows=canonical(n,flat)
        if rows is not None:
            scope=tuple(a for a,_ in rows)
            groups[scope].add(sum(bit<<j for j,(_,bit) in enumerate(rows)))
    steps=[]
    while True:
        if any(len(denied)==1<<len(scope) for scope,denied in groups.items()):
            return Reduction(n,dict(groups),steps,True)
        for scope in groups:
            exterior=row_basis(n,(a for s in groups if s!=scope for a in s))
            shared,private,s_coeff,p_coeff=scope_split(n,scope,exterior)
            if not private:
                continue
            grouped=defaultdict(set)
            for code in groups[scope]:
                grouped[values(s_coeff,code)].add(values(p_coeff,code))
            blocked={s for s,words in grouped.items() if len(words)==1<<len(private)}
            steps.append(Step(exterior,shared,private,dict(grouped)))
            del groups[scope]
            if blocked:
                groups[shared].update(blocked)
            break
        else:
            return Reduction(n,dict(groups),steps)


def solve_cnf(n, clauses, xor_rows=(), *, residual_seed=None):
    """Return an original witness and the reduction, or (None,reduction) on UNSAT."""
    clauses=tuple(tuple(c) for c in clauses)
    xor_rows=tuple(xor_rows)
    if type(n) is not int or n<0 or any(type(l) is not int or not 1<=abs(l)<=n for c in clauses for l in c):
        raise ValueError("invalid dimension or literal")
    chart=solve(n,xor_rows)
    if chart is None:
        return None,None
    origin,kernel=chart
    flats=[]
    for c in clauses:
        flats.append([(_image(1<<(abs(l)-1),kernel),int(l<0)^((origin>>(abs(l)-1))&1)) for l in c])
    d=len(kernel)
    red=reduce_flats(d,flats)
    if red.impossible:
        return None,red
    if residual_seed is None:
        if not red.groups:
            residual_seed=0
        else:
            from clause_rank_drop_hybrid import count
            normals=sorted({a for scope in red.groups for a in scope})
            index={a:d+j+1 for j,a in enumerate(normals)}
            eq=[(a | (1<<(index[a]-1)),0) for a in normals]
            cnf=[tuple(-index[a] if code>>j&1 else index[a] for j,a in enumerate(scope))
                 for scope,codes in red.groups.items() for code in codes]
            _,extended,_=count(d+len(normals),cnf,eq,group_equal=True)
            if extended is None:
                return None,red
            residual_seed=extended & ((1<<d)-1)
    seed=red.lift(residual_seed)
    result=origin^_combination(kernel,seed)
    assert all(any(bool(result>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
    assert all(dot(a,result)==b for a,b in xor_rows)
    return result,red
