"""Exact finite rank-five ghost search; requires python-sat."""
from itertools import product
from pysat.solvers import Solver


class Encoding:
    def __init__(self, rank):
        self.rank = rank
        self.size = 0
        self.clauses = []
        self.true = self.var()
        self.clauses.append([self.true])

    def var(self):
        self.size += 1
        return self.size

    def xor(self, terms):
        ans = -self.true
        for v in terms:
            w = self.var()
            self.clauses.extend([[-ans,-v,-w],[ans,v,-w],[ans,-v,w],[-ans,v,w]])
            ans = w
        return ans

    def span_witness(self, columns, target, enable):
        choices = []
        for vector,present in columns:
            x = self.var()
            self.clauses.append([-x,present])
            choices.append((x,vector))
        for i in range(self.rank):
            v = self.xor([x for x,w in choices if w>>i&1])
            self.clauses.append([-enable,v if target>>i&1 else -v])


def setup(alpha,beta,delta,gamma,rank=5):
    # Coordinate order s,i,k,z,q, with z the contracted ordinary column.
    e = Encoding(rank)
    s,i,k,z,q = 1,2,4,8,1<<(rank-1)
    t = i^k^q^(alpha*z)
    j = s^i^(beta*z)^(gamma*q)
    l = s^k^(delta*z)^(gamma*q)
    others = [(v,w,e.true) for v,w in [(s,0),(i,0),(k,0),(j,0),(l,1)]]
    others.extend((1<<a,0,e.true) for a in range(3,rank-1))
    for v in range(1<<rank):
        for w in (0,1):
            others.append((v,w,e.var()))
    choices = [[],[]]
    for d in range(1<<rank):
        if not (d&s).bit_count()%2 or (d&t).bit_count()%2:
            continue
        dq = (d&q).bit_count()%2
        active = e.var()
        f = [e.var() for _ in range(rank)]
        vals = [e.xor([f[a] for a in range(rank) if v>>a&1]) for v in range(1<<rank)]
        e.clauses.append([-active, vals[t] if dq else -vals[t]])
        e.clauses.append([active,vals[t]])
        eligible = []
        for v,w,p in others:
            if (d&v).bit_count()%2:
                continue
            eligible.append((v,p))
            e.clauses.append([-active,-p, vals[v] if w else -vals[v]])
            e.clauses.append([active,-p,-vals[v]])
        choose = e.var()
        e.clauses.append([-choose,active])
        e.span_witness(eligible,t,choose)
        choices[dq].append(choose)
    e.clauses.extend(choices)
    return e,others,t


def main():
    import sys
    rank=int(sys.argv[1]) if len(sys.argv)>1 else 5
    limit=1<<(rank-4)
    for params in product(range(limit),range(limit),range(limit),range(2)):
        e,others,t = setup(*params,rank=rank)
        with Solver(name='cadical195',bootstrap_with=e.clauses) as solver:
            if solver.solve():
                model = set(solver.get_model())
                selected = [(v,w) for v,w,p in others if p in model]
                print("counterexample",params,t,selected)
                return
    print(f"All {2*limit**3} normalized rank-{rank} chart types are UNSAT.")


if __name__ == '__main__':
    main()
