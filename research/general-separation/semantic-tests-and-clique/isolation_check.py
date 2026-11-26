"""Independent finite checks of rooted cuts and bounded-weight tour isolation."""
from collections import Counter
from itertools import permutations, product
from random import Random


def directed_tours(rows):
    n = len(rows)
    edge_index = {(u,v):j for j,(u,v) in enumerate((u,v) for u in range(n) for v in rows[u])}
    tours = []
    for rest in permutations(range(1,n)):
        path = (0,) + rest
        edges = list(zip(path,path[1:]+(0,)))
        if all(uv in edge_index for uv in edges):
            tours.append(tuple(sorted(edge_index[uv] for uv in edges)))
    return sorted(tours),edge_index


def check_parity(rows, weights, tours, edge_index):
    cut_counts = Counter()
    for targets in product(*rows):
        if len(set(targets)) != len(rows):
            continue
        weight = sum(weights[edge_index[u,v]] for u,v in enumerate(targets))
        for other_colors in product((0,1), repeat=len(rows)-1):
            colors = (0,) + other_colors
            if all(colors[u] == colors[v] for u,v in enumerate(targets)):
                cut_counts[weight] += 1
    direct = Counter(sum(weights[e] for e in tour) for tour in tours)
    assert all((cut_counts[t]-direct[t])%2 == 0 for t in cut_counts.keys() | direct.keys())


def isolator(tours, w):
    ordered = sorted((sum(w[e] for e in T),T) for T in tours)
    if ordered and (len(ordered)==1 or ordered[0][0] < ordered[1][0]):
        return ordered[0][1]
    return None


def positive_box(rows, palette, powers=False):
    tours, edges = directed_tours(rows)
    m = len(edges)
    assert tours and palette >= 2
    images = set()
    for w in product(range(1,palette),repeat=m):
        weights = tuple(1 << a for a in w) if powers else w
        T = min(tours,key=lambda t:(sum(weights[e] for e in t),t))
        out = tuple(val - (i in T) for i,val in enumerate(w))
        final = tuple(1 << a for a in out) if powers else out
        assert isolator(tours,final) == T
        assert tuple(val + (i in T) for i,val in enumerate(out)) == w
        assert out not in images
        images.add(out)
    assert len(images) == (palette-1)**m
    return len(tours),len(images)



def compressed_sum(ranks, bits):
    """Each input token physically occupies one column, regardless of value."""
    capacity = sum(1 << j for j in ranks)
    columns = [[] for _ in range(capacity.bit_length() + 1)]
    for j, b in zip(ranks,bits):
        columns[j].append(b)
    cells = 0
    for j, col in enumerate(columns):
        while len(col) >= 3:
            a, b, c = col.pop(), col.pop(), col.pop()
            col.append(a ^ b ^ c)
            columns[j+1].append((a & b) | (a & c) | (b & c))
            cells += 1
    assert sum(len(c) << j for j,c in enumerate(columns)) == capacity
    assert cells == len(ranks)-sum(map(len,columns))
    assert len(columns[-1]) == 0
    # Finish by a serial carry adder over the two remaining rows.
    carry = 0
    result = 0
    for j,col in enumerate(columns):
        a, b = (col+[0,0])[:2]
        result |= (a ^ b ^ carry) << j
        carry = (a & b) | (a & carry) | (b & carry)
    assert carry == 0
    return result


def main():
    rng = Random(62519)
    stats = Counter()
    def test(rows, category):
        tours, edges = directed_tours(rows)
        m = len(edges)
        stats[category] += 1
        stats['yes_graphs'] += bool(tours)
        stats['multiple_tours'] += len(tours)>1
        for w in [[0]*m,[1]*m] + [[rng.randrange(K) for _ in range(m)] for K in (2,3,5)]:
            check_parity(rows,w,tours,edges)
            stats['rooted_parity_vectors'] += 1

    for n in range(1,8):
        for _ in range(14):
            rows = [tuple(rng.sample(range(n),rng.randrange(min(2,n)+1))) for _ in range(n)]
            test(rows,'general_2out')
    for n in (4,8):
        for _ in range(32):
            p = list(range(n))
            rng.shuffle(p)
            labels = list(range(n))
            rng.shuffle(labels)
            tau = {}
            for j in range(0,n,4):
                block = labels[j:j+4]
                tau.update(zip(block,block[1:]+block[:1]))
            test([tuple((p[i],p[tau[i]])) for i in range(n)],'pure4')
    # Complete directed triangle (both tours); one looped singleton; pure-four cover pair.
    examples = [[(1,2),(0,2),(0,1)],[(0,)],[(0,1),(1,2),(2,3),(3,0)]]
    for rows in examples:
        for K in (2,3,4):
            tours, images = positive_box(rows,K)
            stats['positive_box_images'] += images
            stats['positive_box_cases'] += 1
            _, images = positive_box(rows,K,powers=True)
            stats['power_box_images'] += images
    for n in range(6):
        for ranks in product(range(3),repeat=n):
            for bits in product((0,1), repeat=n):
                assert compressed_sum(ranks,bits) == sum(b << j for b,j in zip(bits,ranks))
                stats['compressor_exhaustive'] += 1
    for _ in range(300):
        ranks = [rng.randrange(16) for _ in range(rng.randrange(1,90))]
        bits = [rng.randrange(2) for _ in ranks]
        assert compressed_sum(ranks,bits) == sum(b << j for b,j in zip(bits,ranks))
        stats['compressor_random'] += 1
    assert stats['multiple_tours'] and stats['rooted_parity_vectors']
    print(dict(sorted(stats.items())))


if __name__ == '__main__':
    main()
