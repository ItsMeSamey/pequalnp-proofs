"""Seeded native CNF+XOR portfolio cross-check. Each invocation runs one bounded batch."""
import argparse
import hashlib
import json
from itertools import combinations,product
from pathlib import Path
from random import Random


def pigeon(p,h):
    events=[[(-1 if (u+2*j)%3==0 else 1)*(u*h+j+1) for j in range(h)] for u in range(p)]
    clauses=list(events)
    for group in [*events,*zip(*events)]:
        clauses.extend((-a,-b) for a,b in combinations(group,2))
    return clauses


def fixtures(seed,count):
    yield "inconsistent-xors",3,[],[(5,0),(5,1)],["brute"]
    yield "xor-only-sat",4,[],[(9,1),(6,0)],["brute"]
    for odd in (False,True):
        clauses=[]
        for v in range(3):
            ids=[2*((v-1)%3)+1,2*((v-1)%3)+2,2*v+1,2*v+2]
            for word in product(range(2),repeat=4):
                a,b,c,d=word
                if ((a&b)^(c&d))!=(odd and v==0):
                    clauses.append(tuple(-i if bit else i for i,bit in zip(ids,word)))
        yield "and-tseitin-"+("odd" if odd else "even"),6,clauses,[],["anf"] if odd else ["anf","brute"]
    yield "signed-fphp-4-into-3",12,pigeon(4,3),[],["resource"]
    yield "signed-fphp-3-into-3",9,pigeon(3,3),[],["choice"]
    yield "signed-choice-xor-sat",6,pigeon(2,3),[(1,1),(2,1)],["choice","brute"]
    yield "signed-choice-xor-unsat",6,pigeon(2,3),[(1,0),(2,1)],["choice","brute"]
    for bit in (0,1):
        yield "horn-"+("sat" if bit else "unsat"),4,[(-1,-2,3),(-3,4)],[(1,1),(2,1),(8,bit)],["horn"]
        yield "horn-support-"+("sat" if bit else "unsat"),6,[(-i,i-1) for i in range(2,7)]+[tuple(range(1,7))],[(1,bit)],["semilattice"]
        cube=[tuple(-i if w>>(i-1)&1 else i for i in (1,2,3)) for w in range(8)]
        yield "semantic-tree-"+("sat" if bit else "unsat"),4,cube[:-1] if bit else cube,[(12,0)],["tree"]
    edges=[(v,(v+1)%5) for v in range(5)]+[(v,5) for v in range(5)]
    events=[[(-1 if (v+c)%2 else 1)*(3*v+c+1) for c in range(3)] for v in range(6)]
    wheel=list(events)+[(-a,-b) for row in events for a,b in combinations(row,2)]
    wheel += [(-events[u][c],-events[v][c]) for u,v in edges for c in range(3)]
    yield "wheel-five-rim-3colour",18,wheel,[],["resource","choice","brute"]
    rng=Random(seed)
    for j in range(count):
        n=rng.randint(3,7)
        cs=[tuple(i*rng.choice((-1,1)) for i in rng.sample(range(1,n+1),3)) for _ in range(rng.randint(n,4*n))]
        rs=[(rng.randrange(1,1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))]
        yield f"mixed-3cnf-{j:03d}",n,cs,rs,None


def valid(x,cs,rs):
    return all(any((x>>(abs(v)-1)&1)==(v>0) for v in c) for c in cs) and all((x&m).bit_count()%2==b for m,b in rs)


def main():
    from sat_xor_driver import solve_sat_xor
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--seed",type=int,default=817739)
    p.add_argument("--start",type=int,default=0)
    p.add_argument("--limit",type=int,default=8)
    p.add_argument("--random",type=int,default=18)
    p.add_argument("--jsonl",type=Path)
    args=p.parse_args()
    if not (0<=args.random<=128 and 0<=args.start and 1<=args.limit<=16):p.error("batch parameters out of range")
    cases=list(fixtures(args.seed,args.random))[args.start:args.start+args.limit]
    results=[]
    for name,n,cs,rs,stages in cases:
        if name=="wheel-five-rim-3colour":
            count=sum(all(colors[i]!=colors[(i+1)%5] and colors[i]!=colors[5] for i in range(5))
                      for colors in product(range(3),repeat=6))
            oracle="proper-colourings-3^6"
        else:
            assert n<=16
            count=sum(valid(x,cs,rs) for x in range(1<<n))
            oracle="original-Boolean-cube"
        budgets=({"resource":1.0,"choice":1.0,"brute":8.0} if name=="wheel-five-rim-3colour" else {s:3.0 for s in (stages or ("anf","horn","choice","resource","semilattice","tree","brute"))})
        result=solve_sat_xor(n,cs,rs,stages=stages,budgets=budgets)
        expected="SAT" if count else "UNSAT"
        assert result["status"]==expected,(name,expected,result)
        witness=result["witness"]
        assert ((isinstance(witness,int) and 0<=witness<1<<n and valid(witness,cs,rs)) if count else witness is None)
        assert all(report["status"] not in ("ERROR","TIMEOUT") for report in result["reports"]),(name,result)
        if stages==["semilattice"]:
            assert any("peak" in r["metrics"] for r in result["reports"] if r["stage"]=="semilattice"),result
        encoded=json.dumps([n,cs,rs],separators=(",",":")).encode()
        results.append(dict(case=name,seed=args.seed,input_sha256=hashlib.sha256(encoded).hexdigest(),
                            n=n,clauses=len(cs),xor_rows=len(rs),models=count,stages=stages or "default",
                            status=expected,witness=witness,oracle=oracle,explicit_budgets=budgets,reports=result["reports"],metrics=result["metrics"]))
    if args.jsonl:
        with args.jsonl.open("w") as out:
            for r in results:out.write(json.dumps(r,sort_keys=True,default=str)+"\n")
    print("Verified",len(results),"cases from index",args.start,[(v["case"],v["status"]) for v in results])


if __name__=="__main__":
    main()
