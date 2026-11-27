"""Construct and verify the fixed-reservoir reduction; original payload starts at site 9."""
from functools import reduce
from itertools import combinations
from operator import xor
from random import Random
from exterior_chart_dp import bits, dot, image, ordered_components

FIXTURE = (170,449,240,81,300,341,174,327,178)
B = [row & 7 for row in FIXTURE[3:]]
INNER = [row >> 3 for row in FIXTURE[3:]]


def signal(v):
    return v & 5, v >> 1


def color_sum(colors,z):
    return reduce(xor,(colors[i] for i in bits(z)),0)


def representatives():
    table = {}
    for u in range(64):
        s = color_sum(B,u)
        for t in range(8):
            if all(dot(INNER[i],u) == dot(B[i],t) for i in bits(u)):
                table.setdefault((s,t),u)
    return table


def host(A,colors):
    rows = list(FIXTURE)+[0]*len(A)
    def edge(i,j):
        rows[i] ^= 1 << j
        rows[j] ^= 1 << i
    for i,v in enumerate(colors):
        r,t = signal(v)
        for j in bits(r):
            edge(i+9,j)
        for j,b in enumerate(B):
            if dot(t,b):
                edge(i+9,j+3)
        for j in range(i):
            if (A[i] >> j & 1) ^ dot(v&3,colors[j]&3):
                edge(i+9,j+9)
    return rows


def check_case(A,colors):
    rows = host(A,colors)
    wanted = {z for z in range(1 << len(A)) if color_sum(colors,z) == 4 and not z & image(A,z)}
    u = representatives()[7,5]
    derived = set()
    for z in range(1 << len(A)):
        for inner in range(64):
            w = 7 | (inner << 3) | (z << 9)
            if not w & image(rows,w):
                assert color_sum(B,inner) == 7
                derived.add(z)
        if z in wanted:
            w = 7 | (u << 3) | (z << 9)
            assert not w & image(rows,w)
    assert derived == wanted
    return wanted


def literal(A):
    colors = [1,2,7]+[0]*(len(A)-3)
    rows = host(A,colors)
    # Eliminate the fixed-pin equations in the identity pin-to-port chart.
    H = [(rows[i+9] >> 9) ^ sum(dot(signal(v)[1],signal(w)[0]) << j
         for j,w in enumerate(colors)) for i,v in enumerate(colors)]
    blocks = list(ordered_components(H))
    ranks = [(block,(block & 7).bit_count()) for block in blocks]
    heavy = next((block for block,r in ranks if r == 3), None)
    truth = check_case(A,colors)
    if heavy is not None:
        keep = list(bits(heavy))
        smaller = [sum(((A[i] >> j)&1) << pos for pos,j in enumerate(keep)) for i in keep]
        projected = check_case(smaller,[colors[i] for i in keep])
        lifts = {sum(1 << keep[i] for i in bits(z)) for z in projected}
        assert lifts <= truth
        assert {z & heavy for z in truth} == lifts
        for i in keep:
            assert not H[i] & ~heavy
        return "heavy",len(A)-len(keep),bool(truth)
    return "low",0,bool(truth)


def check():
    table = representatives()
    allowed = {(s,t) for s in range(8) for t in range(8) if not dot(s,t)}
    assert set(table) == allowed - {(3,7)}
    assert not check_case([],[]) and not check_case([0],[1])
    assert check_case([0],[4]) == {1}
    rng = Random(3141)
    outcomes = set()
    for n in range(3,7):
        for sample in range(12):
            A = [0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2) and not (sample%2 and max(i,j)>=3):
                    A[i] |= 1 << j
                    A[j] |= 1 << i
            check_case(A,[rng.randrange(8) for i in A])
            mode,removed,yes = literal(A)
            outcomes.add((mode,yes))
            if removed:
                outcomes.add(("pruned",yes))
    assert literal([10,9,8,7,0]) == ("heavy",1,False)
    assert literal([2,1,0]) == ("low",0,False)
    assert literal([0,0,0,0]) == ("heavy",1,True)
    assert {("heavy",True),("heavy",False),("low",False),("pruned",True)} <= outcomes
    print("35 reservoir states; fixed six-bit inner selection",table[7,5],
          "; 48 general and 48 literal cases; modes",sorted(outcomes))


if __name__ == "__main__":
    check()
