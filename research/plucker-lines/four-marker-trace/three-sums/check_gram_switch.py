from itertools import combinations, product

def test(parts):
    edges=[(i,j) for i,j in combinations(range(len(parts)),2) if parts[i]!=parts[j]]
    n=len(parts)
    target=0
    for t in parts:target ^= 1<<t
    cands=[]
    for h in range(1<<n):
        if h.bit_count()>4:continue
        t=0
        for i,j in enumerate(parts):
            if h>>i&1:t^=1<<j
        if target==t:cands.append(h)
    checked=0
    for bits in range(1<<len(edges)):
        nbr=[0]*n
        for j,(a,b) in enumerate(edges):
            if bits>>j&1:
                nbr[a]|=1<<b
                nbr[b]|=1<<a
        if any(x.bit_count()%2 for x in nbr):continue
        assert any(all(not(h>>i&1) or not((h&nbr[i]).bit_count()%2)
                       for i in range(n)) for h in cands)
        checked+=1
    return checked
if __name__=='__main__':
    num=0
    for a,b,c in product(range(7),repeat=3):
        if a>=b>=c and 0<a+b+c<=6:
            num+=test([0]*a+[1]*b+[2]*c)
    print(f'Checked {num} labeled Eulerian tripartite graphs through six vertices over canonical part sizes.')
