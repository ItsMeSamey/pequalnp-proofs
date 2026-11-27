"""Check 2,300 fixed-support certificates against independently replayed physical cells."""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from runpy import run_path
from struct import pack

HERE = Path(__file__).resolve().parent
MANIFEST = 'fb9505ff2fb6f39764ce714c6eb4c644b3787910ab4ab93b7a0496021799ed28'


def require(value, message):
    if not value:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON property')
        result[key] = value
    return result


def main():
    base = run_path(str(HERE/'physical.py'))
    require(sha256((HERE/'prefix115.json').read_bytes()).hexdigest()==MANIFEST,
            'wrong prefix manifest')
    base['check_inputs']()
    rows,_ = base['replay']()
    # Table binding uses physical cells, independent of signature representatives.
    table_hash = sha256(b'split25-rows-v1\0')
    for cell,label,sig in rows:
        table_hash.update(pack('>HBI',cell,label,sig))
    positives = sum(1 << c for c,y,s in rows if y)
    features = [sum(1 << c for c,y,s in rows if y and s >> j & 1) for j in range(25)]
    ps,ns = [{s for c,y,s in rows if y==label} for label in (1,0)]
    decreasing = {j for j in range(25)
                  if any(not (s >> j & 1) and (s | 1 << j) in ns for s in ps)}
    require(len(decreasing)==18, 'directions')
    for j in range(25):
        for pop in [ps,ns]:
            require({s>>j&1 for s in pop}=={0,1}, 'old unit')
    @lru_cache(maxsize=None)
    def agreeing(a,b):
        result = positives
        for j in range(25):
            if not ((a^b) >> j & 1):
                result &= features[j] if a >> j & 1 else ~features[j]
        return result

    trace = sha256(b'split25-universal-full-v1\0')
    trace.update(table_hash.digest())
    supports = list(combinations(range(25),3))
    sources = [
        ('ternary-census.json','fbb31f731d20968c974da4f8198de4aa3da1c0e9b931524e2034b3f192f89dee',0,1923),
        ('ternary-suffix.json','ee99568fb2fd3ad3bf5a77970f90a9b96932a659ac4afc56e6ecfe30fd5c26ce',1923,2300),
    ]
    totals = [0]*4
    minima = [1024]*4
    for filename,digest,start,end in sources:
        raw = (HERE/filename).read_bytes()
        require(sha256(raw).hexdigest()==digest,'source commitment mismatch')
        doc = json.loads(raw,object_pairs_hook=unique)
        require(doc['manifest_sha256']==MANIFEST and doc['decreasing']==sorted(decreasing),
                'source table or directional witness mismatch')
        require((doc['first'],doc['next'],doc['stop'])==(start,end,2300) and
                doc['complete'] is (end==2300) and len(doc['records'])==end-start,
                'checkpoint interval discrepancy')
        stats = {}
        for index,record in enumerate(doc['records'],start):
            support,d,target,vertices = record
            require(tuple(support)==supports[index], 'support gap or ordering mismatch')
            require(d==len(decreasing.intersection(support)) and
                    target==(57-len(decreasing)+d)//2+1, 'bad support threshold')
            require(all(type(c) is int and 0 <= c < 1024 and rows[c][1]==0 for c in vertices),
                    'require physical negative cell IDs')
            vertices = sorted(vertices)
            words = [rows[c][2] for c in vertices]
            require(len(vertices)>=target and len(set(words))==len(vertices),'insufficient distinct seeds')
            trace.update(pack('>HH',index,len(vertices)))
            for c in vertices:
                trace.update(pack('>H',c))
            mask = sum(1 << j for j in support)
            buckets = {}
            for s in words:
                key = s & mask
                if key not in buckets:
                    p = positives
                    for j in support:
                        p &= features[j] if s>>j&1 else ~features[j]
                    buckets[key] = p
            for a,b in combinations(words,2):
                candidates = agreeing(min(a,b),max(a,b)) & (buckets[a&mask] | buckets[b&mask])
                require(candidates,'missing promised positive blocker')
                blocker = (candidates & -candidates).bit_length()-1
                t = rows[blocker][2]
                require(rows[blocker][1]==1 and not ((t^a)&~(a^b)) and
                        (t&mask) in (a&mask,b&mask),'invalid reconstructed blocker')
                trace.update(pack('>H',blocker))
            tail = 2*len(vertices)-2+len(decreasing)-d
            require(tail>55, 'certificate does not exclude 55 gates')
            totals[d] += 1
            minima[d] = min(minima[d],tail)
            entry = stats.setdefault(str(d),{'certified':0,'incomplete':0,'smallest_clique':len(words)})
            entry['certified'] += 1
            entry['smallest_clique'] = min(entry['smallest_clique'],len(words))
        require(stats==doc['census'],'wrong published census')
    require(totals==[35,378,1071,816] and minima==[56,57,56,57], 'wrong combined bounds')
    print(json.dumps(dict(table_sha256=table_hash.hexdigest(),witness_sha256=trace.hexdigest(),
                          verified_supports=sum(totals),counts=totals,minimum_tail=minima),
                     sort_keys=True))


if __name__ == '__main__':
    main()
