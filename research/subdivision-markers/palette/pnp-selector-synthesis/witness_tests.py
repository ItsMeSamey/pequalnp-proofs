from random import Random
from recognizer import recognize, selected_sites, solve, tag_at

def span(values):
    result = {0}
    for value in values:
        result |= {old ^ value for old in result}
    return result

def trace(cols, ids):
    return span((cols[i][0] << 4) | (cols[i][1] << 2) | cols[i][2] for i in ids) & set(range(16))

def check():
    random = Random(7605)
    yes = 0
    tested = 0
    for d in range(4):
        for repeat in range(24):
            cols = [(1 << i,random.randrange(4),random.randrange(4)) for i in range(d)]
            cols += [(random.randrange(1 << d),random.randrange(4),random.randrange(4)) for _ in range(5)]
            if repeat % 3 == 0:
                k,b,h=cols[-1]
                cols.append((k,b,h^1))
            target = set(range(4))
            exists = any(trace(cols, [i for i in range(len(cols)) if mask >> i & 1]) == target for mask in range(1 << len(cols)))
            for s in (1,2,3):
                cert = recognize(cols,d,s)
                for chart in range(1 << (2*d)):
                    for anchor, generators in cert.anchors:
                        accum = 0
                        for site in selected_sites(cert,cols,generators,chart):
                            k,b,h=cols[site]
                            assert tag_at(chart,k,d)==b
                            accum ^= k
                        assert accum == anchor
                actual = solve(cols,d,s)
                assert (actual is not None)==exists
                if actual is not None:
                    assert len(actual)<=d+2 and trace(cols,actual)==target
            yes+=exists
            tested+=1
    for omitted,degree,rank in [(set(),2,4),({3,8,11},2,2),({3,8,11},3,4)]:
        cols=[(k,(1^(((k&3)==3)^((k&12)==12)))|(b<<1),random.randrange(4)) for k in range(1,16) if k not in omitted for b in range(2)]
        cert=recognize(cols,4,degree)
        assert len(cert.anchors)==rank
        if rank==2: assert span(a for a,_ in cert.anchors)=={0,3,8,11}
    print(f"{tested} literal physical instances ({yes} YES), three degrees each; three structural ranks passed")

if __name__ == "__main__":
    check()
