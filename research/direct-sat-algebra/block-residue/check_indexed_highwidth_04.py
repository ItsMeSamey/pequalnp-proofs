from itertools import combinations
from unittest.mock import patch

import indexed_ordered_row_csp as indexed
from highwidth_order_fixture import ordered_source
from check_ordered_rows_04 import replay


def main():
    original = indexed.ordered_assignment
    for strict in (False, True):
        calls = []
        def observe(domains, relations, mode):
            assert len(domains) == 10 and all(len(domain) == 4 for domain in domains)
            edges = {(i,j) for i, rel in enumerate(relations) for j in rel if i < j}
            assert len(edges) == 29
            for shore in combinations(range(10), 5):
                a = set(shore)
                b = set(range(10)) - a
                if not all(tuple(sorted((i,j))) in edges for i in a for j in b):
                    continue
                internal = [(i,j) for i,j in edges if i in a and j in a]
                if sorted(sum(i in e for e in internal) for i in a) == [1,1,2,2,2]:
                    break
            else:
                raise AssertionError("recovered interaction graph lacks full K5,5 plus a path")
            calls.append(True)
            return original(domains, relations, mode=mode)
        n,gates,out = ordered_source(5,strict)
        with patch.object(indexed, "ordered_assignment", observe):
            state,stats,raw = indexed.solve(n,gates,output=out)
        assert calls == [True]
        assert stats["method"] == "min" and stats["bad"] == 10
        assert state == ("unsat" if strict else "sat")
        if raw is not None:
            assert replay(raw,gates)[out] == 1 and raw[-1] == 0
            assert [2*raw[2*i]+raw[2*i+1] for i in range(10)] == [0,1,2,3,3]+[3]*5
    print("both K5,5-plus-path extracted graphs, four-state domains, verdicts and raw replay")


if __name__ == "__main__":
    main()
