"""Bounded point-access majority prediction on raw MSB-first NAND circuits.

The learner retains a superset of the genuinely consistent original words:
a sorted short prefix followed by all packed words from tail_start to 2**n-1.
It samples the least min(m,T) candidates and checks every stored mistake
label on each sample (stopping at the first discrepancy). It votes only on
the genuinely viable sample, ties and empty sample voting zero. Every positive
vote exposes a supporting original word, including for the full history at
all-wrong states. On a mistake drop all sampled invalid words and all viable
sample words giving the incorrect vote. Correct feedback is ignored.
Reset does not expand the cube.

For L sampled words and v viable ones, a mistake removes at least
(L-v)+ceil(v/2)>=ceil(L/2). If T>=2, a mistake therefore leaves at most
T-ceil(min(m,T)/2) candidates. One
survivor admits no realizable error. Thus the largest safe T with r errors
remaining satisfies C_0=1, C_r=C_(r-1)+min(C_(r-1)+1,ceil(m/2)). Tightness
for this policy: keep the last packed word as the secret. With t=min(m,T),
query zero on the least ceil(t/2) survivors and one on all larger points.
The predicted zero is wrong and deletes exactly that many. On this particular
stream every untested word lies above the threshold, so every retained word
continues to satisfy all mistake rows. The queries are
ordinary complemented thresholds of O(n) NAND gates when the cap permits.

Writing D_r=C_r+1 yields D_0=2 and D_r=D_(r-1)+min(D_(r-1),ceil(m/2)).
For n>=2, the least m guaranteeing n mistakes is 2**(n-1)+1. At
ceil(m/2)=2**(n-2), C_n=2**n-1; increasing that quota by one suffices.
For n<=1 a budget of one suffices. A small gate cap can exclude the tight
example. The upper bound holds for every cap on realizable streams.

An uncached round uses <=m current evaluations and <=m*r old evaluations
after r mistakes. Even rescanning all
previous gates for each wire costs polynomial(n+s+1) bit operations per
evaluation, where s is the query size. The sample and prefix cost O(m*(n+1))
bits in addition to the stored mistake circuits and evaluation workspace. Large point budgets
can give exponential cost in n. Cache hits still validate and compare the
entire NAND query. The pure replay adapter charges each retained history row.
Cumulative evaluation counters saturate independently at telemetry_cap =
2**(4*n+8). A counter below that cap is exact; per-trial counts stay exact.
When no candidates remain, prediction stays zero and all further feedback
leaves the state unchanged. observe then reports whether the forecast was
wrong, while mistakes and history count only committed state updates.
"""
from itertools import chain

from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate


def _budget(m):
    _natural(m, "point budget")
    if m == 0:
        raise ValueError("point budget must be positive")
    return m


def capacity(m, r):
    """Largest survivor population guaranteed at most r further mistakes."""
    quota = (_budget(m) + 1) // 2
    _natural(r, "remaining mistakes")
    doublings = max(0, (quota - 1).bit_length() - 1)
    initial = 1 << (min(doublings, r) + 1)
    return initial - 1 + max(0, r - doublings) * quota


def mistake_bound(n, m):
    """Worst-case mistakes from the entire cube, for this policy."""
    _natural(n, "arity")
    _budget(m)
    target = 1 << n
    lo, hi = 0, target - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if capacity(m, mid) >= target:
            hi = mid
        else:
            lo = mid + 1
    return lo


class LimitedQueryHalving:
    """predict(q), observe(q,label); an immediately repeated trial is cached."""

    def __init__(self, n, cap, m):
        self.n = _natural(n, "arity")
        self.cap = _natural(cap, "gate cap")
        self.m = _budget(m)
        self._limit = 1 << n
        self.telemetry_cap = 1 << (4 * n + 8)
        self.prefix = ()
        self.tail_start = 0
        self.mistakes = 0
        self.history = ()
        self.last_witness = None
        self.last_points = 0
        self.last_query_evaluations = 0
        self.last_history_evaluations = 0
        self.current_evaluations = 0
        self.history_evaluations = 0
        self.point_evaluations = 0
        self._cache = None

    @property
    def remaining(self):
        return len(self.prefix) + self._limit - self.tail_start

    def _trial(self, q):
        circuit = _source(self.n, q)
        if len(circuit[0]) > self.cap:
            raise ValueError("raw NAND query exceeds the public cap")
        if self.remaining == 0:
            self.last_points = self.last_query_evaluations = self.last_history_evaluations = 0
            self.last_witness = None
            return circuit, 0, (), (), self.tail_start
        if self._cache is not None and self._cache[0] == circuit:
            return self._cache
        count = min(self.m, self.remaining)
        tail_end = self.tail_start + count - len(self.prefix)
        sample = chain(self.prefix, range(self.tail_start, tail_end))
        zeros, ones = [], []
        prior_calls = 0
        for point in sample:
            for prior, label in self.history:
                prior_calls += 1
                if evaluate(self.n, *prior, point) != label:
                    break
            else:
                bit = evaluate(self.n, *circuit, point)
                (ones if bit else zeros).append(point)
        self.last_points = count
        self.last_query_evaluations = len(zeros) + len(ones)
        self.last_history_evaluations = prior_calls
        self.current_evaluations = min(self.telemetry_cap,
                                       self.current_evaluations + self.last_query_evaluations)
        self.history_evaluations = min(self.telemetry_cap, self.history_evaluations + prior_calls)
        self.point_evaluations = min(self.telemetry_cap,
                                     self.point_evaluations + prior_calls + self.last_query_evaluations)
        prediction = int(len(ones) > len(zeros))
        self.last_witness = ones[0] if prediction else None
        self._cache = circuit, prediction, zeros, ones, tail_end
        return self._cache

    def predict(self, q):
        return self._trial(q)[1]

    def observe(self, q, label):
        if type(label) not in (int, bool) or label not in (0, 1):
            raise ValueError("feedback must be a bit")
        circuit, prediction, zeros, ones, tail_end = self._trial(q)
        if prediction == label:
            return False
        if self.remaining == 0:
            return True
        self.prefix = tuple(ones if label else zeros)
        self.tail_start = tail_end
        self.mistakes += 1
        self.history += ((circuit, int(label)),)
        self._cache = None
        return True


def learner_factory(m):
    """Pure predictor(n,cap,history,q), with all rows freshly replayed."""
    _budget(m)

    def forecast(n, cap, history, q):
        learner = LimitedQueryHalving(n, cap, m)
        for prior, label in history:
            learner.observe(prior, label)
        return learner.predict(q)

    return forecast
