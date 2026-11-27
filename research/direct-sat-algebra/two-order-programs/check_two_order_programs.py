"""Small model-set check on explicit indexed three-state programs."""
from itertools import product
from random import Random

def compile_programs(n, clauses):
    variables, clauses_program, equality_program = [], [], []
    for clause in clauses:
        for j, lit in enumerate(clause):
            site = len(variables)
            variables.append(abs(lit)-1)
            last = j+1 == len(clause)
            row = []
            for state in range(3):
                pair = []
                for bit in [0,1]:
                    ok = bool(state) or (bool(bit) == (lit > 0))
                    if state == 2 or (last and not ok):
                        next_state = 2
                    elif last:
                        next_state = 0
                    else:
                        next_state = int(ok)
                    pair.append(next_state)
                row.append(pair)
            clauses_program.append((site,row))
    for i in range(n):
        sites = [j for j,v in enumerate(variables) if v == i]
        if not sites:
            sites = [len(variables)]
            variables.append(i)
            clauses_program.append((sites[0], [(0,0),(1,1),(2,2)]))
        for t,site in enumerate(sites):
            row = [(0,1),(0,1),(2,2)] if t == 0 else [(0,2),(2,1),(2,2)]
            equality_program.append((site,row))
    return variables, (2 if any(not c for c in clauses) else 0,clauses_program), (0,equality_program)

def accepted(program,word):
    state,layers=program
    for j,table in layers:
        state=table[state][(word>>j)&1]
    return state!=2

def main():
    rng=Random(1027)
    cube=list(product((1,-1),(2,-2)))
    cases=[(0,[]),(0,[[]]),(3,[(1,1),(1,-1)]),(2,cube),(2,cube[:-1])]
    for _ in range(85):
        n=rng.randrange(1,4)
        cases.append((n,[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(4))]))
    checked=0
    for n,cs in cases:
        vs,a,b=compile_programs(n,cs)
        assert all(sorted(i for i,_ in pr[1]) == list(range(len(vs))) for pr in [a,b])
        expected=set()
        for x in range(1<<n):
            if all(any(bool((x>>(abs(l)-1))&1)==(l>0) for l in c) for c in cs):
                expected.add(sum(((x>>v)&1)<<i for i,v in enumerate(vs)))
        actual={w for w in range(1<<len(vs)) if accepted(a,w) and accepted(b,w)}
        assert expected==actual
        checked+=1<<len(vs)
    print(len(cases),"complete model sets;",checked,"physical words")

if __name__=="__main__":
    main()
