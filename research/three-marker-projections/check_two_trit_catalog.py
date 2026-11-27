"""Check an eight-track native cap for each named two-trit relation orbit."""
from itertools import permutations
from pathlib import Path

def accepting_mask(wiring, rotations):
    assert sorted(wiring) == list(range(8))
    assert all(len(set(rot)) == 3 and all(0 <= t < 8 for t in rot)
               for rot in rotations)
    truth = 0
    for aux in range(1 << len(rotations)):
        cap = list(wiring)
        for i, rot in enumerate(rotations):
            if aux >> i & 1:
                action = dict(zip(rot, rot[1:] + rot[:1]))
                cap = [action.get(t,t) for t in cap]
        for a in range(3):
            for b in range(3):
                v = 6
                while True:
                    if v < 3:
                        v = (v+a) % 3
                    elif v < 6:
                        v = 3+(v-3+b) % 3
                    v = cap[v]
                    if v == 7:
                        truth |= 1 << (a+3*b)
                        break
                    if v == 6:
                        break
    return truth

def main():
    covered = set()
    perms = list(permutations(range(3)))
    for line in Path(__file__).with_name('two_trit_catalog.txt').read_text().splitlines():
        truth, count, *rest = line.split()
        mask, k = int(truth,16),int(count)
        data = [int(x) for x in rest]
        assert len(data) == 8+3*k and 0 <= k <= 4
        rot = [data[i:i+3] for i in range(8,len(data),3)]
        assert accepting_mask(data[:8],rot) == mask
        orbit = {sum(1 << (u[i%3]+3*v[i//3]) for i in range(9) if mask>>i&1)
                 for u in perms for v in perms}
        assert orbit.isdisjoint(covered)
        covered |= orbit
    assert covered == set(range(512))
    print('all 512 two-trit relations verified')

if __name__ == '__main__':
    main()
