"""Check every mask and every torus-star deletion in the serial family."""
from check_two_shore_homology import labels


def fixture(k,capped):
    offsets=[1]*k
    if capped:
        offsets=[0]+offsets+[2]
    perm=lambda i:3*(i//3)+(i%3+offsets[i//3])%3
    glue=list(range(3*len(offsets)))
    for j in range(len(offsets)-1):
        a,b=3*j+1,3*j+3
        glue[a],glue[b]=glue[b],glue[a]
    return [glue[perm(i)] for i in range(len(glue))]


def red(piv,x):
    while x and x.bit_length() in piv:x^=piv[x.bit_length()]
    return x


def add(piv,x):
    x=red(piv,x)
    if x:piv[x.bit_length()]=x


def test(k,capped):
    sigma=fixture(k,capped)
    n=len(sigma);m=n//3;end=n-2
    rot=lambda a:3*(a//3)+(a+1)%3
    edge=lambda j,a:1<<(6*a+j)
    B=labels(sigma);W=labels([sigma[rot(a)] for a in range(n)])
    if 2+2*m-len(set(B))-len(set(W))!=2*k:raise AssertionError('genus')
    if capped and (B[0]==B[end] or W[0]==W[end]):raise AssertionError('root disks')
    cells={}
    for a in range(n):
        for side,out in enumerate((a,rot(a))):
            add(cells,edge(0,a)^edge(2+side,a)^edge(4+side,a))
            add(cells,edge(1,out)^edge(2+side,sigma[out])^edge(4+side,a))
    z=edge(2,0)^edge(3,0)^edge(2,end)^edge(3,end)
    forbidden=range(int(capped),k+int(capped))
    for h in forbidden:
        ids=slice(3*h,3*h+3)
        if len(set(B[ids]))!=1 or len(set(W[ids]))!=1:raise AssertionError('nonparallel arms')
    yes=0;deletions=0
    for mask in range(1<<m):
        route=labels([sigma[rot(a) if mask>>(a//3)&1 else a] for a in range(n)])
        truth=not capped or (mask&1 and not (mask>>(m-1)&1))
        if (route[0]==route[end])!=bool(truth):raise AssertionError('routing')
        for omitted in [-1,*forbidden]:
            piv=cells.copy()
            for a in range(n):
                if a//3!=omitted:add(piv,edge(5-((mask>>(a//3))&1),a))
            feasible=not red(piv,z)
            if feasible!=(bool(truth) and omitted==-1):
                raise AssertionError((k,capped,mask,omitted))
            deletions+=omitted!=-1
        yes+=bool(truth)
    return 1<<m,yes,deletions


if __name__=='__main__':
    totals=[0,0,0]
    for k in range(1,8):
        for capped in [False,True]:
            for i,x in enumerate(test(k,capped)):totals[i]+=x
    print(totals,'masks, joined masks, single-box deletion checks')
