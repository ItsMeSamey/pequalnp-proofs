"""Check native truth tables directly and expand signed-input symmetries."""
from itertools import permutations
from pathlib import Path

def truth_table(wiring, first, second):
    assert len(wiring) in (12, 15, 24)
    assert sorted(wiring) == list(range(len(wiring)))
    assert 0 <= first < len(wiring) and 0 <= second < len(wiring)
    ans = 0
    for mask in range(1 << (len(wiring)//3)):
        site = first
        while True:
            gate, socket = divmod(site, 3)
            if (mask >> gate) & 1:
                socket = (socket + 1) % 3
            site = wiring[3*gate + socket]
            if site == second:
                ans |= 1 << (mask & 15)
                break
            if site == first:
                break
    return ans

def main():
    transforms = [[sum(((word >> i) & 1) << p[i] for i in range(4)) ^ s
                   for word in range(16)]
                  for p in permutations(range(4)) for s in range(16)]
    covered = set()
    by_switch_count = {}
    path = Path(__file__).with_name('four_complete_catalog.txt')
    for line in path.read_text().splitlines():
        truth, r, t, *indices = line.split()
        mask = int(truth, 16)
        wiring = [int(v) for v in indices]
        assert truth_table(wiring, int(r), int(t)) == mask
        support = [i for i in range(16) if (mask >> i) & 1]
        orbit = {sum(1 << p[i] for i in support) for p in transforms}
        assert covered.isdisjoint(orbit)
        covered |= orbit
        by_switch_count.setdefault(len(wiring)//3,set()).update(orbit)
    print({n:len(v) for n,v in by_switch_count.items()})
    print('covered',len(covered),'missing',len(set(range(65536))-covered))
    assert covered == set(range(65536))
    return covered

if __name__ == '__main__':
    main()
