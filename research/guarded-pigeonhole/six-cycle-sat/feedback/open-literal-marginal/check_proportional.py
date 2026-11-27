"""Count complete physical masks for signed exact-one gadgets."""
from collections import Counter
from itertools import permutations, product
from check import compile_open


def exact_program(n,triples):
    clauses=[]; shallow=[];occs=0
    for a,b,c in triples:
        shallow.append(occs)
        clauses.extend([(a,b,c),(-a,-b),(-a,-c),(-b,-c)])
        occs+=9
    gates,links,_,_,s,t=compile_open(n,clauses)
    # Original three-way tree puts its first occurrence at depth one.
    # Pad that branch with one fork and one merge. Its dead sibling has
    # separate external terminals rather than a wire between fork and merge.
    for h in shallow:
        inp,out=3*h+1,3*h+2
        before=next(w for w,v in links.items() if v==inp)
        after=links[out]
        fork,merge=3*gates,3*gates+3
        gates+=2
        links[before]=fork; links[fork]=inp
        links[out]=merge; links[merge+1]=after
    return gates,links,s,t,occs


def physical_counts(n,triples):
    gates,links,s,t,q=exact_program(n,triples)
    observed=Counter()
    def walk(x,used,mask):
        h,j=divmod(x,3)
        for bit in (0,1):
            if used>>h&1 and ((mask>>h)&1)!=bit:continue
            v=3*h+(j+bit)%3
            newused=used|1<<h;newmask=mask|(bit<<h)
            if v in links:walk(links[v],newused,newmask)
            elif v==t:
                assignment=sum(((newmask>>(q+2*i))&1)<<i for i in range(n))
                observed[assignment]+=1<<(gates-newused.bit_count())
    walk(s,0,0)
    return observed


def actual(n,triples,a):
    return all(sum(((a>>(abs(v)-1))&1)==(v>0) for v in c)==1 for c in triples)


def and_block(x,y,z,q00,q01,q10):
    return [(-x,q10,z),(x,q00,q01),(-y,q01,z),(y,q00,q10)]


if __name__=='__main__':
    total=0
    for c in product((1,-1,2,-2,3,-3),repeat=3):
        found=physical_counts(3,[c])
        expected={a:16 for a in range(8) if actual(3,[c],a)}
        if found!=expected:raise AssertionError((c,found,expected))
        total+=sum(found.values())
    for x,y in [(1,2),(1,1),(1,-1),(-2,-1)]:
        clauses=and_block(x,y,3,4,5,6)
        found=physical_counts(6,clauses)
        expected={a:16**4 for a in range(64) if actual(6,clauses,a)}
        if found!=expected or len(found)!=4:raise AssertionError((x,y,found))
        for a in found:
            truth=lambda v:bool((a>>(abs(v)-1))&1)==(v>0)
            if truth(3)!=(truth(x) and truth(y)):raise AssertionError(a)
    clauses=and_block(1,2,3,4,5,6)+[(-3,-3,3)]
    if sum(physical_counts(6,clauses).values())!=16**5:raise AssertionError('forcing')
    print('216 signed triples including repeats,',total,'successful masks; four AND variants and forced output')
