from itertools import combinations,product
from random import Random
from forced_edge_affine import solve


def main():
    rng=Random(582)
    checks=0
    for _ in range(18):
        edges=[(a,b,(rng.randrange(3),rng.randrange(3))) for a in range(2)
               for b in range(2,4) for _ in range(rng.randrange(3))]
        match=[ids for ids in combinations(range(len(edges)),2)
               if len({v for i in ids for v in edges[i][:2]})==4]
        for t in product(range(3),repeat=2):
            good=[ids for ids in match if all(sum(edges[i][2][j] for i in ids)%3==v for j,v in enumerate(t))]
            s,w,_=solve(4,edges,t)
            assert (s!="SAT" or tuple(sorted(w)) in good) and (s!="UNSAT" or not good)
            checks+=1
    # Two private blocks at each paired endpoint, with dense invertible recoding.
    d=8
    mix=[[int(i==j) for j in range(d)] for i in range(d)]
    for _ in range(4*d*d):
        i,j=rng.sample(range(d),2)
        mix[i]=[(a+b)%3 for a,b in zip(mix[i],mix[j])]
    def encode(x):
        return tuple(sum(a*b for a,b in zip(row,x))%3 for row in mix)
    edges=[]
    for i in range(d//2):
        for a,b in ((0,0),(1,0),(0,1)):
            x=[0]*d
            x[2*i:2*i+2]=a,b
            edges.append((i,i+d//2,encode(x)))
    target=encode((0,1)*(d//2))
    s,w,info=solve(d,edges,target)
    assert s=="SAT" and info["initial_rank"]==d and info["ranks"]==[0]
    s,w,info=solve(d,edges,encode((1,1)+(0,1)*(d//2-1)))
    assert s=="UNSAT"
    print(checks,"brute targets and two dense rank-eight private-coordinate cases passed")


if __name__=="__main__":
    main()
