"""Small original-seed oracles for the conditional forecast driver.

Exhaustive truth-table learners here take exponential time in raw input width.
"""
from itertools import product

from forecast_consistency_search import decide, solve
from odd_masked_circuit import compile_source


def raw(n,q,x):
    values = {-1:0,-2:1}
    for i in range(n):
        values[i] = (x >> (n-1-i)) & 1
    for w,(a,b) in enumerate(q[0],n):
        values[w] = int(not (values[a] and values[b]))
    return values[q[1]]


class Oracle:
    def __init__(self,twist=False,poison=False):
        self.rows = {}
        self.calls = []
        self.twist = twist
        self.poison = poison

    def mask(self,n,q):
        key = n,q
        if key not in self.rows:
            self.rows[key] = sum(raw(n,q,x) << x for x in range(1 << n))
        return self.rows[key]

    def vote(self,n,h,q):
        live = (1 << (1 << n))-1
        for m,b in h:
            live &= m if b else ~m
        if not live:
            return 0
        if self.twist and n == 2 and not h and q == 9:
            return 0
        if self.twist and n == 2 and h == ((9,1),):
            # Tie on the two surviving words. Both choices are singly
            # feasible, but the threshold forecasts T0=0,T1=1 conflict.
            if q == 1:
                return 0
            if q == 3:
                return 1
        ones = (live&q).bit_count()
        margin = 2*ones-live.bit_count()
        return int(margin > 0 or (margin == 0 and bool((live & -live)&q)))

    def __call__(self,n,cap,history,query):
        assert len(query[0]) <= cap
        h = tuple((self.mask(n,p),int(b)) for p,b in history)
        q = self.mask(n,query)
        if self.poison and any(self.vote(n,h[:i],p) == b for i,(p,b) in enumerate(h)):
            raise AssertionError('a correct clone forecast was committed or a mistake repeated')
        # Ensure first F forecast at reset in the dedicated fixture is 0.
        if self.twist and n == 2 and not h and q == 9:
            result = 0
        else:
            result = self.vote(n,h,q)
        self.calls.append((n,h,q,result))
        return result


def source(n,bits):
    gates = []
    def nand(a,b):
        gates.append((a,b))
        return n+len(gates)-1
    def neg(a):
        return nand(a,a)
    out = -1
    for x in range(1 << n):
        if bits >> x & 1:
            term = -2
            for i in range(n):
                literal = i if x >> (n-1-i) & 1 else neg(i)
                term = neg(nand(term,literal))
            out = nand(neg(out),neg(term))
    return tuple(gates),out


def check_modes(n,F):
    words = [x for x in range(1 << n) if raw(n,F,x)]
    for mode in ('one','two','positive'):
        predictor = Oracle(poison=True)
        assert decide(n,F,predictor,mode) == bool(words)
        predictor.calls.clear()
        result = solve(n,F,predictor,mode)
        assert result['status'] == ('witness' if words else 'unsat')
        if words:
            assert result['assignment'] in words
        assert result['forecasts'] == len(predictor.calls)
        assert result['max_history'] >= max((len(h) for _,h,_,_ in predictor.calls), default=0)


def false_crossing():
    F = source(2,9)
    model = Oracle(twist=True,poison=True)
    assert decide(2,F,model,'positive')
    h = ((9,1),)
    assert (2,h,1,0) in model.calls and (2,h,3,1) in model.calls
    assert any(history == h+((1,1),) for _,history,_,_ in model.calls)
    assert not any((1,0) in history or (3,1) in history for _,history,_,_ in model.calls)
    # T0=1 retains only original 0. T0=0 plus T1=1 (clone predictions
    # recorded as feedback) would instead require the nonmodel 1.
    assert 9 & 1 == 1 and not (9 & ~1 & 3)
    assert 9 & ~1 == 8  # recording T0=0 alone already discards witness 0
    assert solve(2,F,Oracle(twist=True,poison=True),'positive')['assignment'] in (0,3)


def refuse():
    for mode in ('one','two','positive'):
        for bad in ('1',2,None):
            def wrong(*unused):
                return bad
            for fn in (decide,solve):
                try:
                    fn(2,source(2,9),wrong,mode)
                except ValueError:
                    pass
                else:
                    raise AssertionError('invalid nonbit accepted')


if __name__ == '__main__':
    for n in range(3):
        for mask in range(1 << (1 << n)):
            check_modes(n,source(n,mask))
    check_modes(4,compile_source(1,((),0)))
    false_crossing()
    refuse()
    print('Conditional reductions, original witnesses, and clone histories agree.')
