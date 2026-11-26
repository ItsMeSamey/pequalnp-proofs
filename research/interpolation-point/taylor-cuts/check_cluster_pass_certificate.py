from copy import deepcopy
from random import Random
from cluster_pass_certificate import produce,verify


def main():
    rng=Random(7301)
    accepted=rejected=0
    for i in range(100):
        n=rng.randrange(5)
        size=rng.randrange(2,5)
        order=list(range(1,n+1))
        rng.shuffle(order)
        passes=[]
        for j in range(rng.randrange(1,6)):
            forward=rng.choice((True,False))
            gates=[]
            for v in (order if forward else reversed(order)):
                for _ in range(rng.randrange(3)):
                    gates.append((rng.choice((-v,v)),rng.sample(range(size),size),rng.sample(range(size),size)))
            passes.append((forward,gates))
        groups=[1]*len(passes) if i%2 else [len(passes)]
        args=(n,size,passes,order,groups)
        start=rng.choice([None,*range(size)])
        closing=rng.sample(range(size),size)
        expected=False
        for mask in range(1<<n):
            for s in range(size) if start is None else (start,):
                t=s
                for _,gates in passes:
                    for lit,p,q in gates:
                        t=(p,q)[((mask>>(abs(lit)-1))&1)^(lit<0)][t]
                expected |= closing[t]==s
        cert=produce(*args,start=start,closing=closing)
        assert (cert[0]=="sat")==expected and verify(*args,cert,start=start,closing=closing)
        if expected:
            accepted+=1
            assert not verify(*args,("sat",1<<n,cert[2]),start=start,closing=closing)
        else:
            rejected+=1
            bad=deepcopy(cert)
            bad[1][0][0].clear()
            assert not verify(*args,bad,start=start,closing=closing)
    # Identity has two fixed points, so its trace vanishes over F2 while it is SAT.
    args=(1,2,[(True,[])],[1],[1])
    assert produce(*args)[0]=="sat"
    fake=("unsat",[[[0]],[[0]]],[[],[]])
    assert not verify(*args,fake)
    assert not verify(*args,("sat",0,1),start=0)
    print(accepted,"SAT and",rejected,"UNSAT proofs matched brute-force, altered proofs rejected")


if __name__=="__main__":
    main()
