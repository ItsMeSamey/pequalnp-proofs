"""Independent bank-first release check for the size-18 eight-input census."""
import sys
FULL=(1<<64)-1
H=[sum(1<<p for p in range(64) if p>>i&1) for i in range(6)]

def check(gates, demand):
    signed=[(u&h,u&(FULL^h)) for u,h in zip(gates,H)]
    branches={k for pair in signed for k in pair}
    mandatory=set(gates)-branches-{FULL}
    budget=3-len(mandatory)
    def reachable(helpers):
        known={FULL}
        pending=set(helpers)
        while True:
            enabled={x|y for x in known for y in known} & pending
            pending-=enabled
            for i,u in enumerate(gates):
                if u in known:enabled.update(signed[i])
            if enabled<=known:break
            known|=enabled
        return not pending and all(u in known for u in gates)
    def feasible_receivers(bases):
        ds=sorted({FULL^(x|y) for x in bases for y in bases if (x|y)!=FULL and (x|y) not in (branches|mandatory)},key=int.bit_count)
        minimal=[]
        for d in ds:
            if not any((q&d)==q for q in minimal):minimal.append(d)
        def solve(pool, target):
            if not target:return True
            if len(pool)<target or sum(d.bit_count() for d in pool[:target])>64:return False
            pivot=pool[0]&-pool[0]
            hit=[d for d in pool if d&pivot]
            miss=[d for d in pool if not d&pivot]
            return solve(miss,target) or any(solve([e for e in miss if not e&d],target-1) for d in hit)
        return solve(minimal,demand)
    tested=0
    reachable_count=0
    def enumerate_banks(aux, previous):
        nonlocal tested,reachable_count
        tested+=1
        bank=branches|mandatory|aux
        if reachable(mandatory|aux):
            reachable_count+=1
            if feasible_receivers(bank):return True
        if len(aux)==budget:return False
        candidates=sorted({x|y for x in bank for y in bank if (x|y)>previous and (x|y) not in bank and (x|y)!=FULL})
        return any(enumerate_banks(aux|{c},c) for c in candidates)
    result=enumerate_banks(set(),0)
    return int(result),tested,reachable_count

for row in sys.stdin:
    nums=list(map(int,row.split()))
    print(nums[0],*check(nums[1:],int(sys.argv[1])),flush=True)
