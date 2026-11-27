"""Seeded finite controls for internal edge pivots on the 13-site obstruction."""
from random import Random
from rooted_full_boundary_solver import edge_pivot, bits, mask, image
from three_pin_template_solver import basis_of

TEMPLATE = [6372,1572,4107,1828,640,8011,161,3665,1064,4282,6570,1185,1573]
PINS = (8,9,10)
SEED = 265317


def reached(start, allowed, neighbors):
    seen = 1 << start
    queue = [start]
    for v in queue:
        fresh = neighbors(v) & allowed & ~seen
        seen |= fresh
        queue.extend(bits(fresh))
    return seen


def prime(A):
    # A module containing root must be closed under v -> every outside site
    # distinguishing root from v. Every pair generates the full graph exactly
    # when this implication digraph is strongly connected for each root.
    full = (1 << len(A))-1
    for root,r in enumerate(A):
        live = full ^ (1 << root)
        start = next(bits(live))
        if reached(start,live,lambda v: A[v]^r) != live:
            return False
        if reached(start,live,lambda w: A[w] ^ (full if r >> w & 1 else 0)) != live:
            return False
    return True


def cutrank(A,S):
    return len(basis_of(A[i]&~S for i in bits(S)))


def check(t):
    rng = Random(SEED+t)
    bags = []
    n = 0
    for i in range(len(TEMPLATE)):
        size = 1 if i in PINS else t
        bags.append(list(range(n,n+size)))
        n += size
    bagmasks = list(map(mask,bags))
    def draw():
        A = [0]*n
        for i,bag in enumerate(bags):
            outside = 0
            for j in bits(TEMPLATE[i]):
                outside |= bagmasks[j]
            for u in bag:
                A[u] = outside
            for local,u in enumerate(bag):
                for v in bag[:local]:
                    if ((local==1 and v==bag[0]) or rng.randrange(2)):
                        A[u] |= 1<<v
                        A[v] |= 1<<u
        final = A
        active = []
        for i,bag in enumerate(bags):
            if i in PINS:
                active.append(bagmasks[i])
                continue
            a,b = bag[:2]
            active.append((bagmasks[i] & ~(A[a]^A[b])) | (1<<a) | (1<<b))
            final = edge_pivot(final,a,b)
        return A,final,active
    for attempt in range(1,200):
        A,F,alpha = draw()
        if (prime(F) and all(reached(b[0],bm,lambda v:F[v])==bm for b,bm in zip(bags,bagmasks))
                and all(alpha[i].bit_count() >= max(2,t//4) for i in range(13) if i not in PINS)):
            break
    else:
        raise AssertionError("seeded fixture search exhausted")
    for i,bag in enumerate(bags):
        external = 0
        for j in bits(TEMPLATE[i]):
            external |= alpha[j]
        for u in bag:
            assert F[u]&~bagmasks[i] == (external if alpha[i]>>u&1 else 0)
    # Direct symbolic parity projection: on each bag internal degree sums cancel;
    # arbitrary external drift factors through selected active-vertex parities.
    fixed = mask(PINS)
    assert not any((x&fixed)==fixed and not x&image(TEMPLATE,x) for x in range(1<<13))
    full = (1<<n)-1
    for _ in range(36):
        x = rng.getrandbits(n)
        z = mask(i for i,h in enumerate(alpha) if (h&x).bit_count()%2)
        y = image(F,x)
        assert mask(i for i,h in enumerate(bagmasks) if (x&h&y).bit_count()%2) == z&image(TEMPLATE,z)
        S = rng.getrandbits(n) & full
        assert cutrank(A,S) == cutrank(F,S)
    pins = mask(bags[i][0] for i in PINS)
    free = full ^ pins
    pin_rows = [F[p]&free for p in bits(pins)]
    assert len(basis_of(pin_rows)) == 3
    passed = 0
    for _ in range(256):
        sites = rng.sample(list(bits(free)),max(2,t//8))
        normals = pin_rows + [1<<v for v in sites] + [F[v]&free for v in sites]
        passed += len(basis_of(normals)) == len(normals)
    print("t",t,"vertices",n,"draw",attempt,"minimum active",
          min(alpha[i].bit_count() for i in range(13) if i not in PINS),
          "sampled jointly independent",passed,"/ 256")
    assert passed == 256


if __name__ == "__main__":
    for size in (8,16,32):
        check(size)
