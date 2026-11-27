"""Independent physical-fibre successor checkpoint. Run with assertions enabled."""
from itertools import combinations
from padding_cnf import encode
from support_probe import probe_support
from monotone_affine_probe import probe

def decode(raw):
    lines = raw.splitlines()
    assert lines[0] == b'p cnf 22 13'
    rows = [tuple(map(int, line.split())) for line in lines[1:]]
    assert len(rows) == 13 and all(len(r) == 4 and r[-1] == 0 for r in rows)
    assert {r[:3] for r in rows[:8]} == {
        tuple(-v if w >> j & 1 else v for j, v in enumerate((5, 6, 7)))
        for w in range(8)}
    key = 0
    for i, row in enumerate(rows[8:]):
        v = 8 + 3*i
        assert row[:3] in ((-v, v+1, v+2), (v, -v-1, v+2))
        key |= int(row[0] < 0) << i
    return key

def check(name, phase, invoke, status, keys, reason=None):
    submissions, predictions = [], []
    def construct(k):
        raw = encode([], 4, k)
        submissions.append(raw)
        return raw
    def predict(raw):
        predictions.append(raw)
        return int(phase(decode(raw)))
    r = invoke(construct, predict)
    assert r['status'] == status and r.get('reason') == reason
    assert submissions == predictions and list(map(decode, predictions)) == keys
    if 'calls' in r:
        assert r['calls'] == len(keys) and r['input_bytes'] == sum(map(len, predictions))
        assert r['work'] == dict.fromkeys(('construct_calls','predict_calls'), len(keys))
        if status == 'disagreement':
            assert list(r['formulas']) == [predictions[0], predictions[-1]]
            assert list(r['keys']) == [0, keys[-1]]
            assert list(r['predictions']) == [phase(0),phase(keys[-1])] and phase(0)!=phase(keys[-1])
    else:
        assert [s['physical'] for s in r['samples']] == predictions
        assert all(s['key']==decode(s['physical']) and s['prediction']==phase(s['key']) for s in r['samples'])
    print(name, status, len(keys), sum(map(len, predictions)))

ball = [sum(1<<i for i in s) for d in range(6) for s in combinations(range(5), d)]
def support(d, cap=None):
    return lambda c,p: probe_support(5,d,c,p,query_cap=cap)
def aff(nodes):
    return lambda c,p: probe(5,nodes,c,p,promised=True)
quadratic = lambda x: (x.bit_count()*(x.bit_count()-1)//2)%2
check('quadratic', quadratic, support(2),'disagreement',ball[:7])
check('singleton-miss', lambda x:x==31,support(4),'unknown',ball[:-1])
check('singleton-hit', lambda x:x==31,support(5),'disagreement',ball)
check('high-degree', lambda x:x&3==3 or x==28,support(2),'disagreement',ball[:7])
check('cap', quadratic,support(2,6),'unknown',ball[:6])
check('infeasible',lambda x:1,aff([('leaf',1,0),('leaf',1,1),('or',0,1)]),'unknown',[],'infeasible endpoint')
check('mismatch',lambda x:1-(x&1),aff([('leaf',1,0)]),'unknown',[0,1],'endpoint mismatch')
check('pair',lambda x:x&1,aff([('leaf',1,0)]),'pair',[0,1])
