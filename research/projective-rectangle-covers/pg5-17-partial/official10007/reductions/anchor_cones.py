"""Check row-mask covers or exhaustive binary owner-bit refutations for one fixed shore."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ROWS = json.loads((ROOT / 'rows.json').read_text())
N = len(ROWS)
FULL = (1 << N) - 1
INC = [sum(1 << i for i, row in enumerate(ROWS) if row >> j & 1) for j in range(N)]

def bits(mask):
    while mask:
        b = mask & -mask
        yield b
        mask -= b

def check(ok, why):
    if not ok:
        raise ValueError(why)

def shore(x):
    return type(x) is int and 0 <= x <= FULL

def columns(left):
    return sum(1 << j for j, incident in enumerate(INC) if not left & incident)

def propagate(on, off):
    """Return True if the partial membership assignment entails a conflict."""
    while True:
        changed = False
        for incident in INC:
            alive = [t for t, mask in enumerate(on) if not mask & incident]
            for p in bits(FULL ^ incident):
                owners = [t for t in alive if not off[t] & p]
                if not owners:
                    return True
                if len(owners) == 1:
                    t = owners[0]
                    # This owner must cover the positive support point, and its
                    # shore must omit all six points incident with this column.
                    if not on[t] & p or off[t] & incident != incident:
                        on[t] |= p
                        off[t] |= incident
                        changed = True
        if not changed:
            return False

def reject_tree(node, on, off):
    closed = propagate(on, off)
    if node is None:
        check(closed, 'open leaf')
        return 1
    check(not closed and isinstance(node, list) and len(node) == 4, 'invalid split')
    t, i, zero, one = node
    check(type(t) is int and 0 <= t < len(on) and type(i) is int and 0 <= i < N, 'bad owner index')
    b = 1 << i
    check(not (on[t] | off[t]) & b, 'branch is already fixed')
    lo, hi = off.copy(), on.copy()
    lo[t] |= b
    hi[t] |= b
    return reject_tree(zero, on.copy(), lo) + reject_tree(one, hi, off.copy())

def main():
    p = argparse.ArgumentParser()
    p.add_argument('file', type=Path)
    p.add_argument('--budget', type=int, default=17)
    p.add_argument('--anchor', type=int, default=55, help='fixed first row mask, or -1 for unanchored controls')
    args = p.parse_args()
    k, a = args.budget, args.anchor
    check(k > 0 and (a == -1 or shore(a)), 'invalid parameters')
    data = json.loads(args.file.read_text())
    if 'shores' in data:
        s = data['shores']
        check(isinstance(s,list) and len(s)<=k and all(shore(x) for x in s), 'bad shores')
        check(a==-1 or a in s, 'fixed anchor omitted')
        cov = [0]*N
        for left in s:
            right = columns(left)
            for b in bits(left):
                cov[b.bit_length()-1] |= right
        check(cov == [FULL ^ row for row in ROWS], 'missing a zero cell')
        print(f'verified {len(s)} closed rectangles, 775 zero cells')
    else:
        check(set(data)=={'tree'}, 'expected shores or tree')
        on, off = [0]*k, [0]*k
        if a != -1:
            on[0], off[0] = a, FULL ^ a
        leaves = reject_tree(data['tree'], on, off)
        print(f'verified exhaustive refutation, anchor {a}, budget {k}, {leaves} leaves')
if __name__=='__main__':
    main()
