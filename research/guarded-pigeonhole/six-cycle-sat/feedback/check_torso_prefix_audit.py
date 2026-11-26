"""Check representative-based Pfaffian prefix transfers against every mask."""
from functools import lru_cache
from itertools import combinations
from random import Random


def pf(rows):
    @lru_cache(None)
    def rec(mask):
        if not mask:
            return 1
        bit = mask & -mask
        rest = mask ^ bit
        neighbors = rows[bit.bit_length()-1] & rest
        ans = 0
        while neighbors:
            mate = neighbors & -neighbors
            ans ^= rec(rest ^ mate)
            neighbors ^= mate
        return ans
    return rec


def reduce_vector(x, pivots):
    coord = 0
    while x and x.bit_length() in pivots:
        y, c = pivots[x.bit_length()]
        x ^= y
        coord ^= c
    return x, coord


def signature_function(rows, cut):
    basis, pivots = [], {}
    for row in rows[cut:]:
        column = row & ((1<<cut)-1)
        z, _ = reduce_vector(column,pivots)
        if z:
            pivots[z.bit_length()] = z,0
            basis.append(column)
    border = [row & ((1<<cut)-1) for row in rows[:cut]]
    for j,column in enumerate(basis):
        for i in range(cut):
            if column>>i&1:
                border[i] |= 1<<(cut+j)
        border.append(column)
    evaluate = pf(border)
    faces = [s for s in range(1<<len(basis)) if s.bit_count()%2==0]
    def signature(mask):
        return sum(evaluate(mask | (s<<cut))<<i for i,s in enumerate(faces))
    return signature


def check(rows):
    reps, states = [0],[1]
    for gate in range(len(rows)//2):
        sig = signature_function(rows,2*gate+2)
        next_reps, pivots = [],{}
        columns = [[],[]]
        for b in (0,1):
            for mask in reps:
                child = mask | ((3*b)<<(2*gate))
                s = sig(child)
                z, coord = reduce_vector(s,pivots)
                if z:
                    label = 1<<len(next_reps)
                    next_reps.append(child)
                    pivots[z.bit_length()] = z, coord^label
                    coord = label
                columns[b].append(coord)
        new = []
        for b in (0,1):
            for coeff in states:
                target = 0
                for i,col in enumerate(columns[b]):
                    if coeff>>i&1:
                        target ^= col
                new.append(target)
        reps,states = next_reps,new
    direct = pf(rows)
    for mask, value in enumerate(states):
        ids = sum(3<<(2*i) for i in range(len(rows)//2) if mask>>i&1)
        if value != direct(ids):
            raise AssertionError((rows,mask,value))
    return len(states)


if __name__ == "__main__":
    rand = Random(55170)
    total = 0
    for trial in range(300):
        g = 1+trial%6
        rows = [0]*(2*g)
        for i,j in combinations(range(2*g),2):
            if rand.randrange(4) < 1+trial%3:
                rows[i] ^= 1<<j
                rows[j] ^= 1<<i
        total += check(rows)
    print(f"300 matrices; {total} coefficients reproduced")
