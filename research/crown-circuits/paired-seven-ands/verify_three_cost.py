from itertools import combinations_with_replacement, combinations
from three_templates import minimum_unions
n=4
singles=frozenset(1<<j for j in range(n))
front={singles}
costs={}
for cost in range(7):
    nxt=set()
    for available in front:
        for goal in combinations_with_replacement(sorted(available),3):
            costs.setdefault(goal,cost)
        if cost<6:
            for a,b in combinations(available,2):
                if a|b not in available:nxt.add(available|{a|b})
    front=nxt
for goal in combinations_with_replacement(range(1,1<<n),3):
    assert minimum_unions(goal)==costs[goal],(goal,minimum_unions(goal),costs[goal])
print(len(costs),'four-literal demand triples agree with breadth-first enumeration')
