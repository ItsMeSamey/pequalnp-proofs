"""Check the projected21 first-fork lower bound without third-party dependencies."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


source = (root / 'paid26-alias-ac6.json').read_bytes()
require(hashlib.sha256(source).hexdigest() == '16199778bdce2ba5ae48b6c55ec730f73f7059c0e58857ec7fa837f9b58f8879', 'source digest')
care = dict(json.loads(source)['care'])
outside = 27
bits = [j for j in range(21) if not outside & (1 << j)]
for j in range(21):
    step = 1 << j
    signs = {v for a,v in care.items() if not a & step and care.get(a | step) == 1-v}
    require(len(signs) == (2 if j in bits else 1), 'essentiality or binateness')


def incompatible(edge_list, colors):
    order = sorted(bits, key=lambda j: -sum(1/e.bit_count() for e in edge_list if e & (1 << j)))
    incident = {j: [e for e in edge_list if e & (1 << j)] for j in bits}

    def search(i, groups):
        if i == len(order):
            return True
        j = order[i]
        for k,g in enumerate(groups):
            new = g | (1 << j)
            if all(e & new != e for e in incident[j]):
                if search(i+1, groups[:k] + [new] + groups[k+1:]):
                    return True
            if g == 0:
                break
        return False

    require(not search(0, [0]*colors), 'admissible coloring exists')


general = []
for mask, observations in json.loads((root/'projected-orientation-witness07.json').read_text()).items():
    coords = 0
    facts = []
    for a,j,b,k in observations:
        require(j in bits and k in bits and not a & (1 << j) and not b & (1 << k), 'edge bases')
        require(care[a] != care[a | (1 << j)] and care[b] != care[b | (1 << k)], 'edge must change label')
        coords |= (a ^ b) | (1 << j) | (1 << k)
        facts.append((min(j,k),max(j,k),care[a]^care[b]))
    require(coords == int(mask) and not coords & outside, 'varying coordinates')
    if len(facts) == 1:
        j,k,v = facts[0]
        require(j == k and v == 1, 'single relative-sign contradiction')
    else:
        require(len(facts) == 2 and facts[0][:2] == facts[1][:2] and facts[0][2] != facts[1][2], 'opposite relative signs required')
    general.append(coords)
incompatible(general, 4)

monotone = []
for a,b,c,d in json.loads((root/'projected-three-group07.json').read_text())['witnesses']:
    require(a & b == a and c & d == c and [care[x] for x in (a,b,c,d)] == [0,1,1,0], 'opposing monotone edges')
    varying = (a | b | c | d) ^ (a & b & c & d)
    require(not varying & outside, 'outside slots differ')
    monotone.append(varying)
incompatible(monotone, 5)
