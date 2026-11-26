from random import Random

def score_circuits(points):
    sums, gains = [0], [0]
    circuits = []
    for i,(col,label) in enumerate(points):
        sums.extend([v^col for v in sums])
        gains.extend([v^label for v in gains])
    for s in range(1,len(sums)):
        if sums[s] == 0 and not any(c&s==c for c,_ in circuits):
            circuits.append((s,gains[s]))
    return circuits

rng=Random(872)
for trial in range(200):
    a,h,j = rng.sample(range(1,16),3)
    plane={0,h,j,h^j}
    cap=[(1,a^v) for v in plane]
    for _ in range(rng.randint(1,7)):
        cap.append((rng.randint(1,7),rng.randrange(16)))
    raw=score_circuits(cap)
    other=[v for v in cap if v[0]!=1]
    proj=lambda z:min(z^v for v in plane)
    compressed=[(1,16|proj(a))]+[(col,proj(g)) for col,g in other]
    compressed_cs=score_circuits(compressed)
    for t in range(1,16):
        wanted=any((S&15) and g==t and S.bit_count()>=3 for S,g in raw)
        got=any(g==16|proj(t) for _,g in compressed_cs)
        assert wanted==got
print('200 projected matroids and all 15 target residues agree on the plane branch')
