"""Exact original-assignment forecasts using independently recognized range counters.

posterior() conditions on all supplied rows. TailRangeForecast retains only
mistakes and learner_factory replays that state. max_latents caps 2**m per
nonempty range; an unknown result carries no forecast and never commits state.
"""
from forecast_consistency_search import threshold
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate
from tail_permutation_range import recognize


def _bit(value):
    if type(value) not in (int, bool) or value not in (0, 1):
        raise ValueError('expected a binary label')
    return int(value)


def _cut(h, circuit):
    """Recognize exactly the raw threshold() serialization without listing cutoffs."""
    gates, out = circuit
    if not gates:
        return {-1: -1, -2: (1 << h)-1}.get(out)
    start, previous, j = 0, -2, 0
    for i in reversed(range(h)):
        wire = h + start
        if gates[start:start+2] == ((previous, previous), (i, wire)):
            j |= 1 << (h-1-i)
            start += 2
        elif gates[start:start+3] == ((i, i), (wire, previous), (wire+1, wire+1)):
            start += 3
        else:
            return None
        previous = h + start-1
    return j if start == len(gates) and out == previous and circuit == threshold(h, j) else None


def _conjunction(h, rows):
    """Intern ordered NANDs across the frozen system, retaining original inputs."""
    gates, interned = [], {}

    def nand(a, b):
        key = a, b
        if key not in interned:
            interned[key] = h + len(gates)
            gates.append(key)
        return interned[key]

    def inv(a):
        return -3-a if a in (-1,-2) else nand(a, a)

    operands = []
    for (source, output), label in rows:
        local = []
        def mapped(w):
            return w if w < h else local[w-h]
        for a, b in source:
            local.append(nand(mapped(a), mapped(b)))
        wire = mapped(output)
        operands.append(wire if label else inv(wire))
    out = -2
    for wire in dict.fromkeys(operands):
        if wire == -1:
            return (), -1
        if wire == -2:
            continue
        out = wire if out == -2 else inv(nand(out, wire))
    return tuple(gates), out


def posterior(h, history, query, *, max_latents=None, range_engine=None):
    """Return exact counts and original witnesses, or a structured budget refusal.

    For m the maximum of the two independently selected enumeration widths, runtime
    is 2**m times a polynomial in h and the combined raw description length.
    Unrecognized structure can require m=h. Empty intervals need no enumeration.
    """
    _natural(h, 'arity')
    if range_engine is None:
        range_engine = recognize
    if max_latents is not None:
        _natural(max_latents, 'max_latents')
    query = _source(h, query)
    history = tuple((_source(h, row), _bit(label)) for row, label in history)
    low, high = 0, (1 << h)-1
    arbitrary = []
    for row, label in history:
        j = _cut(h, row)
        if j is None:
            arbitrary.append((row, label))
        elif label:
            high = min(high, j)
        else:
            low = max(low, j+1)
    j = _cut(h, query)
    states = []
    widths = []
    for bit in (0, 1):
        lo, hi = low, high
        if j is None:
            system = [*arbitrary, (query, bit)]
        else:
            system = arbitrary
            if bit:
                hi = min(hi, j)
            else:
                lo = max(lo, j+1)
        state = range_engine(h, _conjunction(h, system)) if lo <= hi else None
        states.append((state, lo, hi))
        widths.append(None if state is None else state.m)

    required = max((1 << m for m in widths if m is not None), default=0)
    if max_latents is not None and required > max_latents:
        return dict(status='unknown', reason='latent_budget', required=required,
                    available=max_latents, latent_widths=tuple(widths))
    counts, witnesses = [], []
    for bit, (state, lo, hi) in enumerate(states):
        count = 0 if state is None else state.range_count(lo, hi)
        point = state.witness(lo, hi) if count else None
        if count and (point is None or not lo <= point <= hi or
                      evaluate(h, *query, point) != bit or
                      any(evaluate(h, *row, point) != label for row, label in history)):
            raise AssertionError('original witness failed history or query verification')
        counts.append(count)
        witnesses.append(point)
    prediction = int(counts[1] > counts[0])
    return dict(status='exact', counts=tuple(counts), witnesses=tuple(witnesses),
                prediction=prediction, witness=witnesses[prediction], latent_widths=tuple(widths))


class TailRangeForecast:
    """Exact majority over original assignments consistent with mistaken rows."""
    def __init__(self, h, cap, *, max_latents=None, range_engine=None):
        self.h = _natural(h, 'arity')
        self._range_engine = range_engine
        self.cap = _natural(cap, 'gate cap')
        self.max_latents = None if max_latents is None else _natural(max_latents, 'max_latents')
        self.history = ()
        self._cache = None
        self._empty = False

    def _trial(self, query):
        query = _source(self.h, query)
        if len(query[0]) > self.cap:
            return query, dict(status='unknown', reason='gate_budget', required=len(query[0]), available=self.cap)
        if self._cache is not None and self._cache[0] == query:
            return self._cache
        if self._empty:
            result = dict(status='exact', counts=(0, 0), witnesses=(None, None),
                          prediction=0, witness=None, latent_widths=(None, None))
        else:
            result = posterior(self.h, self.history, query, max_latents=self.max_latents,
                               range_engine=self._range_engine)
        self._cache = query, result
        return self._cache

    def predict(self, query):
        _, result = self._trial(query)
        return result['prediction'] if result['status'] == 'exact' else result.copy()

    def observe(self, query, label):
        label = _bit(label)
        circuit, result = self._trial(query)
        if result['status'] == 'unknown':
            return result.copy()
        if result['prediction'] == label:
            return False
        if not self._empty:
            self.history += ((circuit, label),)
            self._empty = result['counts'][label] == 0
        self._cache = None
        return True


def learner_factory(max_latents=None, *, range_engine=None):
    """Replay raw labeled rounds; propagate UNKNOWN immediately on budget refusal."""
    if max_latents is not None:
        _natural(max_latents, 'max_latents')

    def forecast(h, cap, history, query):
        learner = TailRangeForecast(h, cap, max_latents=max_latents, range_engine=range_engine)
        for row, label in history:
            corrected = learner.observe(row, label)
            if isinstance(corrected, dict):
                return corrected
        return learner.predict(query)
    return forecast
