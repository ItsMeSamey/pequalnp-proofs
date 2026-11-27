"""Exact scalar field-quadratic fibers with binary affine pins.

ScalarForm(field,squares,cross) represents sum squares[i]*x_i^2 plus
sum cross[i,j]*x_i*x_j over a supplied binary field with identity 1.
Packed inputs concatenate field coordinates starting at low bits. Pins
are (input mask, rhs bit). count accepts point_count(field,D) for the
number of projective rational points of y^2+xy=x^3+D^2. The default
enumerates the field and is exponential in its binary degree. A supplied
polynomial-time point counter yields 2^h times polynomial counting work.
plane_witness is independent of point counting.
"""
from itertools import combinations
from punctured_witness import BinaryField
from quadratic_image import bits, gauss, parity
from quadratic_target import affine_domain, insert, reduce_vector


def small_field_point_count(field, d):
    """Exhaustively count by x and the binary quadratic equation for y/x."""
    if not 0 < d < field.size:
        raise ValueError("curve parameter must be nonzero")
    count = 2  # x=0 and the point at infinity
    for x in range(1, field.size):
        # Tr(x+d²/x²)=Tr(x+d/x)
        if not field.trace(x ^ field.mul(d, field.inverse(x))):
            count += 2
    return count


class ScalarForm:
    def __init__(self, field, squares, cross):
        self.field = field
        self.squares = tuple(squares)
        self.d = len(self.squares)
        self.n = self.d * field.m
        if any(not 0 <= i < j < self.d for i,j in cross):
            raise ValueError("invalid mixed coefficient indices")
        if any(not 0 <= v < field.size for v in (*self.squares, *cross.values())):
            raise ValueError("invalid field coefficient")
        self.cross = {e: v for e,v in cross.items() if v}
        units = tuple(1 << i for i in range(self.n))
        self.polar_dual = {}
        linears = sum(field.trace(self.evaluate(u)) << i for i,u in enumerate(units))
        pair_set = set()
        for i,u in enumerate(units):
            col = 0
            for j,v in enumerate(units):
                if field.trace(self.polar(u,v)):
                    col |= 1 << j
                    if j > i:
                        pair_set.add((i,j))
            insert(col,u,self.polar_dual)
        if len(self.polar_dual) != self.n:
            raise ValueError("degenerate scalar polar")
        self.bias = gauss(self.n, (0,linears,frozenset(pair_set)))

    def chunks(self, x):
        return [(x >> (i*self.field.m)) & (self.field.size-1) for i in range(self.d)]

    def scale(self, a, x):
        return sum(self.field.mul(a,v) << (i*self.field.m) for i,v in enumerate(self.chunks(x)))

    def evaluate(self, x):
        f = self.field
        v = self.chunks(x)
        y = 0
        for a,u in zip(self.squares, v):
            y ^= f.mul(a,f.mul(u,u))
        for (i,j),a in self.cross.items():
            y ^= f.mul(a,f.mul(v[i],v[j]))
        return y

    def polar(self, x, y):
        f = self.field
        xx, yy = self.chunks(x), self.chunks(y)
        out = 0
        for (i,j),a in self.cross.items():
            out ^= f.mul(a, f.mul(xx[i],yy[j]) ^ f.mul(xx[j],yy[i]))
        return out

    def _checks(self, target, pins):
        if not 0 <= target < self.field.size:
            raise ValueError("invalid field target")
        rows = {}
        for mask, rhs in pins:
            if not 0 <= mask < 1 << self.n or rhs not in (0,1):
                raise ValueError("invalid binary pin")
            r, c = reduce_vector(mask, rows)
            if r:
                rows[r.bit_length()-1] = r, rhs ^ c
            elif rhs ^ c:
                return None
        reduced = tuple(rows.values())
        dual = [reduce_vector(row, self.polar_dual)[1] for row,_ in reduced]
        return reduced, dual

    def count(self, target, pins=(), *, point_count=None):
        checked = self._checks(target, pins)
        if checked is None:
            return 0
        reduced, dual = checked
        rhs = sum(c << i for i,(_,c) in enumerate(reduced))
        f = self.field
        backend = small_field_point_count if point_count is None else point_count
        cache = {}
        total = 0
        for s in range(1 << len(dual)):
            w = 0
            for i in bits(s):
                w ^= dual[i]
            u = self.evaluate(w)
            if not u and not target:
                value = f.size-1
            elif not u or not target:
                value = -1
            else:
                d = f.mul(u, target)
                if d not in cache:
                    num = backend(f, d)
                    if not isinstance(num,int):
                        raise TypeError("point_count must return an integer projective point count")
                    cache[d] = num - f.size - 1
                value = cache[d]
            total += -value if parity(s & rhs) else value
        result, rem = divmod((1 << self.n) + self.bias*total, f.size << len(dual))
        if rem or not 0 <= result <= 1 << (self.n-len(dual)):
            raise ArithmeticError("inconsistent point counts for scalar fiber")
        return result

    def plane_witness(self, target, pins=()):
        """Return a checked witness when the orthogonal space contains a plane.

        None means inconsistent pins or no such plane. For consistent pins
        with d > 2*rank(pins), every target is guaranteed a witness.
        """
        checked = self._checks(target, pins)
        if checked is None:
            return None
        reduced, dual = checked
        x0, _, _ = affine_domain(self.n, reduced)
        equations = []
        for w in dual:
            columns = [self.polar(w,1 << j) for j in range(self.n)]
            for k in range(self.field.m):
                equations.append((sum(((v >> k) & 1) << j for j,v in enumerate(columns)),0))
        _, basis, _ = affine_domain(self.n, equations)
        plane = next(((u,v) for u,v in combinations(basis,2) if self.polar(u,v)), None)
        if plane is None:
            return None
        u, v = plane
        f = self.field
        inv = f.inverse(self.polar(u,v))
        center = (x0 ^ self.scale(f.mul(self.polar(x0,v),inv),u) ^
                  self.scale(f.mul(self.polar(x0,u),inv),v))
        delta = target ^ self.evaluate(center)
        w = next(x for x in (u,v,u^v) if self.evaluate(x))
        scalar = f.sqrt(f.mul(delta, f.inverse(self.evaluate(w))))
        x = center ^ self.scale(scalar,w)
        if self.evaluate(x) != target or any(parity(x & row)!=c for row,c in reduced):
            raise ArithmeticError("plane witness misses original constraints")
        return x


def check():
    from random import Random
    rng = Random(6719)
    tested = 0
    def direct_curve(f,d):
        # Count pairs directly, plus the unique projective point at infinity.
        return 1 + sum(f.mul(y,y)^f.mul(x,y) == f.mul(x,f.mul(x,x))^f.mul(d,d)
                       for x in range(f.size) for y in range(f.size))
    for p in (7,11):
        f = BinaryField(p)
        for u in range(1,f.size):
            assert small_field_point_count(f,u) == direct_curve(f,u)
        trace_one = next(u for u in range(f.size) if f.trace(u))
        for form in (ScalarForm(f,[0,0],{(0,1):1}),
                     ScalarForm(f,[1,trace_one],{(0,1):1}),
                     ScalarForm(f,[1,0,0,1],{(0,1):1,(2,3):1})):
            models = [form.evaluate(x) for x in range(1 << form.n)]
            r, s = rng.randrange(1,1 << form.n), rng.randrange(1,1 << form.n)
            for pins in ((),((r,1),),((r,1),(r,1)),((r,0),(r,1)),
                         ((r,0),(s,1),(r^s,1)),((0,0),),((0,1),)):
                expected = [0]*f.size
                for x,t in enumerate(models):
                    if all(parity(x&row)==c for row,c in pins):
                        expected[t] += 1
                for t,num in enumerate(expected):
                    assert form.count(t,pins) == form.count(t,pins,point_count=direct_curve) == num
                    x = form.plane_witness(t,pins)
                    reduced = form._checks(t,pins)
                    if reduced is not None and form.d>2*len(reduced[0]):
                        assert x is not None
                    if x is not None:
                        assert models[x]==t and all(parity(x&row)==c for row,c in pins)
                    tested += 1
    print(f"{tested} split/norm/quaternary pin counts and plane witnesses passed")


if __name__ == "__main__":
    check()
