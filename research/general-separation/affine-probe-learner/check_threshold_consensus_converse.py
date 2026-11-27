"""Source-only fixtures for frozen-state threshold decision and self-reduction."""


def decision(n,F,tie_high,stats):
    full = (1 << (1 << n))-1
    history = ()
    def predict(query):
        live = full
        for q,label in history:
            live &= q if label else ~q
        if not live:
            return 0
        anchor = (1 << (live.bit_length()-1)) if tie_high else live & -live
        margin = 2*(live & query).bit_count()-live.bit_count()
        return int(margin > 0 or (margin == 0 and bool(query & anchor)))
    if predict(F):
        stats['immediate'] += 1
        return True
    history = ((F,1),)
    # Exactly one committed row. All later calls interrogate this same state.
    size = 1 << n
    def prefix(j):
        return (1 << (j+1))-1
    if predict(0) or not predict(full):
        return False
    lo,hi = -1,size-1
    while hi-lo > 1:
        mid = (hi+lo)//2
        if predict(prefix(mid)):
            hi = mid
        else:
            lo = mid
    stats['bisections'] += 1
    assert F & ~prefix(lo) & prefix(hi) == 1 << hi
    return bool(F >> hi & 1)


def full_check():
    stats = dict(immediate=0,bisections=0)
    for n in range(4):
        for F in range(1 << (1 << n)):
            for tie_high in (False,True):
                assert decision(n,F,tie_high,stats) == bool(F)
                if not F:
                    continue
                # Decision-only replies, including shortcut YES, recover a
                # witness through fresh calls on half-cube restrictions.
                d,remaining,word = n,F,0
                while d:
                    d -= 1
                    half = 1 << d
                    low = remaining & ((1 << half)-1)
                    next_bit = int(not decision(d,low,tie_high,stats))
                    remaining = (remaining >> half) if next_bit else low
                    word = 2*word+next_bit
                assert F >> word & 1
    assert all(stats.values())
    # Support {1,6}; transition at 4 is singly feasible for every j.
    for j in range(-1,8):
        assert any((x <= j) == (j >= 4) for x in (1,6))
    assert not any(3 < x <= 4 for x in (1,6))


if __name__ == '__main__':
    full_check()
    print('Frozen-state threshold and restart controls passed.')
