from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
from random import Random
import sys
from check_line import direct
from line_trace import produce, verify


def rejects(cols, pins, cert):
    try:
        verify(cols, [1,2,4], pins, cert)
    except (ValueError,KeyError,TypeError):
        return True
    return False


if __name__ == "__main__":
    binary = sys.argv[1]
    rng = Random(98614)
    cases = [([2,3,8,10,12,16,18,32],()),([8,9],()),([0,1,1],(2,)),
             ([3,2],(0,)),([2],()),([0,1],())]
    for _ in range(50):
        n = rng.randrange(3,9)
        cases.append(([rng.randrange(32) for _ in range(n)],tuple(i for i in range(n) if rng.randrange(6)==0)))
    types = Counter()
    orders = Counter()
    controls = []
    for i,(cols,pins) in enumerate(cases):
        cert = json.loads(json.dumps(produce(cols,[1,2,4],pins,executable=binary)))
        answer = verify(cols,[1,2,4],pins,cert)
        assert answer == direct(cols,pins), (cols,pins,cert)
        types[cert["terminal"]] += 1
        for step in cert["steps"]:
            orders[len(step["interface"])] += 1
        if i < 6:
            controls.append(dict(columns=cols,names=[1,2,4],forced=pins,certificate=cert))
    assert set(orders)=={0,1,2} and len(types)==6
    cols = cases[0][0]
    neg = controls[0]["certificate"]
    assert neg["terminal"] == "star" and [len(s["interface"]) for s in neg["steps"]] == [0,1,2]
    mutations = []
    for i in range(3):
        c = deepcopy(neg); c["steps"][i]["keep"].remove(0); mutations.append(c)
    for i in [1,2]:
        c = deepcopy(neg); c["steps"][i]["minimum"]=[]; mutations.append(c)
        c = deepcopy(neg); c["steps"][i]["interface"][0]=0; mutations.append(c)
    c=deepcopy(neg); c["edges"][0]=c["edges"][1]; mutations.append(c)
    assert all(rejects(cols,(),c) for c in mutations)
    if len(sys.argv)>2:
        Path(sys.argv[2]).write_text(json.dumps(controls,indent=2)+"\n")
    print("56 physical cases",dict(types),"split orders",dict(orders),"8 tamper checks passed")
