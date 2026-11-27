"""Compare two-shore mod-2 cellular boundary membership with native trajectories."""
from itertools import combinations_with_replacement, permutations
from random import Random


def labels(p):
    lab=[-1]*len(p)
    for seed in range(len(p)):
        a=seed
        while lab[a]<0:
            lab[a]=seed
            a=p[a]
    return lab


def test(sigma):
    n=len(sigma);g=n//3
    rot=lambda a:3*(a//3)+(a+1)%3
    # Edge coordinates per incoming socket a:
    # I,O = in/out halfwire from switch to midpoint; b,w = mark midpoint to
    # disk centers; B,W = switch-center arms at its two marked-color corners.
    cell=[]
    def edge(i,x):
        return 1<<(6*x+i)
    for a in range(n):
        for side,out in enumerate((a,rot(a))):
            cell.append(edge(0,a)^edge(2+side,a)^edge(4+side,a))
            cell.append(edge(1,out)^edge(2+side,sigma[out])^edge(4+side,a))
    def red(piv,x):
        while x and x.bit_length() in piv:
            x^=piv[x.bit_length()]
        return x
    def add(piv,row):
        x=red(piv,row)
        if x:piv[x.bit_length()]=x
    cellp={}
    for row in cell:add(cellp,row)
    checks=0
    for mask in range(1<<g):
        piv=cellp.copy()
        for a in range(n):
            bit=(mask>>(a//3))&1
            # Black hub on at physical bit 1, white hub on at bit 0.
            add(piv,edge(4+(1-bit),a))
        L=labels([sigma[rot(a) if mask>>(a//3)&1 else a] for a in range(n)])
        for a,b in combinations_with_replacement(range(n),2):
            bridges=edge(2,a)^edge(3,a)^edge(2,b)^edge(3,b)
            if (red(piv,bridges)==0)!=(L[a]==L[b]):
                raise AssertionError((sigma,mask,a,b))
            checks+=1
    return checks


if __name__=='__main__':
    cases=checks=0
    for n in (3,6):
        for p in permutations(range(n)):
            cases+=1;checks+=test(p)
    r=Random(14783)
    for n in (9,12,15):
        for _ in range(45):
            cases+=1;checks+=test(r.sample(range(n),n))
    print(cases,'oriented native charts;',checks,'two-shore tests')
