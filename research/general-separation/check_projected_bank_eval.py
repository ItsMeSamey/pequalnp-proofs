"""Finite EVAL slice with explicit bank DAGs, signed atoms and term-specific branches."""
from collections import Counter
from itertools import product

N = 4
R = (N+6+2)**2
SLOTS = (11,12,13,14)
live = tuple(j*R+s for j,s in enumerate(SLOTS))
# Nodes are four raw inputs then XOR(0,1), AND(0,1).
CIRCUIT = ((6,0,1),(8,0,1))
INDEX = N*R


def raw(i):
    return ('raw',i)


def op(table,a,b):
    return ('gate',table,a,b)


def read(tree,inputs,bank):
    kind = tree[0]
    if kind == 'raw':
        return inputs[tree[1]]
    if kind == 'bank':
        return bank[tree[1]]
    if kind == 'constant':
        return tree[1]
    return (tree[1] >> (2*read(tree[2],inputs,bank)+read(tree[3],inputs,bank))) & 1


def parity(block,alias=None):
    # Balanced XOR tree over the entire raw parity block.
    leaves = [raw(block*R+j) for j in range(R)]
    if alias is not None:
        leaves[SLOTS[block]] = ('bank',alias)
    while len(leaves)>1:
        leaves = [op(6,leaves[j],leaves[j+1]) if j+1<len(leaves) else leaves[j]
                  for j in range(0,len(leaves),2)]
    return leaves[0]


def gate_index(which):
    terms = []
    for i in which:
        t = ('constant',1)
        for j in range(3):
            x = raw(INDEX+j)
            t = op(8,t,x if (i>>j)&1 else op(6,x,('constant',1)))
        terms.append(t)
    t = ('constant',0)
    for q in terms:
        t = op(14,t,q)
    return t


def atom(block,indices,also=None):
    named = live[block]
    if block==1:
        # Two real bank NAND gates, with a repeated parent and fanout.
        gates = ((named,named),(INDEX+3,INDEX+3))
        exports = (INDEX+4,)
    else:
        gates = ()
        # First export bypasses gates. Second is nominated, but never read.
        exports = (named,2*R+1)
    tree = parity(block,0)
    if also is not None:
        tree = op(8,tree,parity(also))
    return gates,exports,op(8,gate_index(indices),tree)


ATOMS = (atom(0,(0,4)),atom(1,(1,4)),atom(2,(2,)),atom(3,(3,)),
         atom(0,(4,),1),atom(1,(5,),0))
COEFF = (1,1,1,1,-2,1)


def footprint(atom):
    gates,exports,tree = atom
    named = {a for pair in gates for a in pair if a<INDEX+3}
    named.update(w for w in exports if w<INDEX+3)
    counts = Counter()
    stack = [tree]
    while stack:
        expr = stack.pop()
        if expr[0]=='raw':
            counts[expr[1]] += 1
        elif expr[0]=='gate':
            stack.extend(expr[2:])
    return named | {w for w,v in counts.items() if v>3}


def bank_values(atom,raw_inputs):
    wires = dict(raw_inputs)
    for w,(a,b) in enumerate(atom[0],INDEX+3):
        wires[w] = 1-(wires[a]*wires[b])
    return tuple(wires[w] for w in atom[1])


def inputs(i,bits):
    # The header and explicit CIRCUIT are common to every index. Here their
    # fixed values are parameters of this evaluation slice.
    row = dict.fromkeys(range(INDEX+3),0)
    row.update(zip(live,bits))
    row.update({INDEX+j:(i>>j)&1 for j in range(3)})
    return row


def oracle(row,i):
    word = [sum(row[j*R+p] for p in range(R))%2 for j in range(N)]
    for table,a,b in CIRCUIT:
        word.append((table>>(2*word[a]+word[b]))&1)
    return word[i] if i<len(word) else 0


def main():
    widths = [footprint(atom) for atom in ATOMS]
    assert live[0] in widths[0] and 2*R+1 in widths[0] and live[1] in widths[1]
    assert live[1] not in widths[0] and live[0] not in widths[1]
    cache = {}
    for i in range(8):
        for bits in product((0,1),repeat=N):
            row = inputs(i,bits)
            vals = [read(a[2],row,bank_values(a,row)) for a in ATOMS]
            assert sum(v*c for v,c in zip(vals,COEFF)) == oracle(row,i)
            cache[i,bits] = vals
        # Also check nontrivial inactive slots on the unprojected slice.
        row = inputs(i,(1,0,1,0))
        for j in range(N):
            row[j*R+1] = 1
        assert sum(c*read(a[2],row,bank_values(a,row)) for a,c in zip(ATOMS,COEFF)) == oracle(row,i)
    for i,term in ((0,(0,)),(4,(0,1)),(4,(0,0,4)),(5,(5,))):
        active = [j for j in range(N) if any(live[j] in widths[a] for a in term)]
        rest = [j for j in range(N) if j not in active]
        total = 0
        for branch in product((0,1),repeat=len(active)):
            bits = [0]*N
            for j,b in zip(active,branch):
                bits[j] = b
            base = inputs(i,bits)
            banks = [bank_values(ATOMS[a],base) for a in term]
            for tail in product((0,1),repeat=len(rest)):
                for j,b in zip(rest,tail):
                    bits[j] = b
                row = inputs(i,bits)
                assert all(bank_values(ATOMS[a],row) == fixed for a,fixed in zip(term,banks))
                total += all(read(ATOMS[a][2],row,fixed) for a,fixed in zip(term,banks))
        direct = sum(all(vals[a] for a in term) for (idx,_),vals in cache.items() if idx==i)
        assert total == direct == (8 if i==0 else 4)
    print('Projected bank outputs, signed indexed EVAL and branch multiplicities agree.')


if __name__=='__main__':
    main()
