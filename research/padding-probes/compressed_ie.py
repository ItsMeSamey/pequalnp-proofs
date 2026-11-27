"""Signed intersection dictionary on free coordinates of a Boolean affine base."""
from event_affine_ie import _insert, _word


class Limit(Exception):
    """A state or work cap prevented exact completion."""


def _meet(key, equations):
    rows = {m.bit_length()-1:(m,b) for m,b in key}
    for m,b in equations:
        if not _insert(rows,m,b):
            return None
    for p in sorted(rows):
        m,b = rows[p]
        for j in rows:
            r,c = rows[j]
            if j > p and r & (1<<p):
                rows[j] = (r^m,c^b)
    return tuple(rows[j] for j in sorted(rows))


class Counter:
    """Work counts old-state intersections and final-state conditioning tests.
    State cap bounds each dictionary, including intermediate next-layer sizes.
    """
    def __init__(self,width,equations,cylinders,*,state_cap=None,work_cap=None):
        for cap in (state_cap,work_cap):
            if cap is not None and (type(cap) is not int or cap < 0):
                raise ValueError("invalid cap")
        if type(width) is not int or width < 0:
            raise ValueError("invalid width")
        self.width = width
        self.work_cap = work_cap
        self.state_cap = state_cap
        self.metrics = dict(peak_states=0,work=0,count_calls=0,projected_cylinders=0,
                            free_bits=0,final_states=0)
        self.states = {}
        equations = tuple(equations)
        if any(m < 0 or m.bit_length()>width or b not in (0,1) for m,b in equations):
            raise ValueError("invalid base equation")
        base = _meet((), equations)
        if base is None:
            return
        pivots = {m.bit_length()-1:(m,b) for m,b in base}
        free = [j for j in range(width) if j not in pivots]
        self.dim = len(free)
        self.metrics['free_bits'] = self.dim
        self.forms = []
        for j in range(width):
            m,b = pivots.get(j,(0,0))
            raw = m ^ (1<<j)
            reduced = sum(((raw>>p)&1)<<i for i,p in enumerate(free))
            self.forms.append((reduced,b))
        projected = {self._project(mask,value) for mask,value in cylinders}
        projected.discard(None)
        self.metrics['projected_cylinders'] = len(projected)
        if () in projected:
            return
        self.states = {():1}
        self._size(self.states)
        for flat in sorted(projected):
            updated = self.states.copy()
            for old,coef in self.states.items():
                self._tick()
                child = _meet(old,flat)
                if child is not None:
                    merged = updated.get(child,0)-coef
                    if merged:
                        updated[child] = merged
                        self._size(updated)
                    else:
                        updated.pop(child,None)
            self.states = updated
            if not updated:
                break
        self.metrics['final_states'] = len(self.states)

    def _size(self, states):
        if self.state_cap is not None and len(states)>self.state_cap:
            raise Limit("state cap",self.metrics.copy())
        self.metrics['peak_states'] = max(self.metrics['peak_states'],len(states))

    def _tick(self):
        if self.work_cap is not None and self.metrics['work']>=self.work_cap:
            raise Limit("work cap",self.metrics.copy())
        self.metrics['work'] += 1

    def _project(self,mask,value):
        if mask < 0 or mask.bit_length()>self.width or value < 0 or value & ~mask:
            raise ValueError("invalid cylinder")
        equations = []
        while mask:
            bit = mask & -mask
            coeff,shift = self.forms[bit.bit_length()-1]
            equations.append((coeff,shift ^ int(bool(value & bit))))
            mask ^= bit
        return _meet((),equations)

    def count(self,pin=0,value=0):
        self.metrics['count_calls'] += 1
        if not self.states:
            return 0,None
        held = self._project(pin,value)
        if held is None:
            return 0,None
        total = 0
        for key,coef in self.states.items():
            self._tick()
            joint = _meet(key,held)
            if joint is not None:
                total += coef << (self.dim-len(joint))
        if total < 0:
            raise ArithmeticError("negative count")
        if not total:
            return 0,None
        coords = _word({m.bit_length()-1:(m,b) for m,b in held})
        candidate = sum((((m&coords).bit_count()%2)^b)<<j for j,(m,b) in enumerate(self.forms))
        return total,candidate

    def witness(self,pin=0,value=0):
        if not self.count(pin,value)[0]:
            return None
        for j in range(self.width):
            bit = 1<<j
            if not pin & bit:
                pin |= bit
                if not self.count(pin,value)[0]:
                    value |= bit
        return value
