def excess(a, b, w):
    return 2 * ((a+w).bit_length() + (b+w).bit_length() - 2) - a - b - w

assert all(excess(a,b,w)<=0 for a in (6,7) for b in range(2,8) for w in range(1,12))
assert all(excess(a,b,w)<=0 for a in range(2,8) for b in range(2,8) for w in range(8,12))
profiles = [(a,b,w) for w in range(1,8) for a in range(2,6) for b in range(a,6) if excess(a,b,w)>0]
assert profiles == [(3,3,1),(2,2,2),(2,3,2),(2,2,3),(3,3,5),(2,2,6),(2,3,6),(2,2,7)]
print(profiles)
