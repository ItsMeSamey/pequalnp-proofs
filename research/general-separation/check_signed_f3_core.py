"""Scheduled integration with the independent original-coordinate oracle."""
import sys
from itertools import combinations
from pathlib import Path
from signed_f3_core import evaluate

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'site-team-01'/'signed-read2'))
from independent_oracle import oracle, verify


def main():
    grid=verify(lambda f,z: evaluate(f,z)['value'])
    clauses=[[] for _ in range(4)]
    for i,(u,v) in enumerate(combinations(range(4),2)):
        clauses[u].append((i,0))
        clauses[v].append((i,1))
    z=[2]*6
    assert oracle(clauses,z)==2
    assert evaluate(clauses,z,max_states=16)==dict(status='exact',value=2)
    for f,p,budget,need in ((clauses,z,15,16),([[(0,1)]],[2],1,2)):
        assert evaluate(f,p,max_states=budget)==dict(status='unknown',reason='state_budget',
                                                    required=need,available=budget)
    for f,p,budget in (([[],[(0,1)]*3],[1],None),([[(0,0),(0,1)],[(0,0)]],[2],None),
                       ([[(1,1)]],[2],None),([[(0,3)]],[2],None),([],[],-1)):
        try:
            evaluate(f,p,max_states=budget)
        except ValueError:
            continue
        raise AssertionError((f,p,budget))
    print(grid,'K4, two refusals and five validation checks passed.')


if __name__=='__main__':
    main()
