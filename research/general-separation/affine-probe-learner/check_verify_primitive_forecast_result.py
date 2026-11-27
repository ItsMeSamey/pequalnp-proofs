"""Serialized result round trips and tampering controls; run as a standalone script."""
import json
from copy import deepcopy
from dataclasses import asdict

from check_primitive_forecast_extractor import N, SOURCE, ZERO, majority
from primitive_forecast_extractor import extract
from primitive_rewrite_chain import public_cap
from verify_primitive_forecast_result import verify_result


def verifier(source, bound, policy):
    cap = public_cap(N,len(source[0]))

    def learner(n,s,history,q):
        assert (n,s) == (N,cap)
        return policy(history,q)

    raw = extract(N,source,cap,bound,learner)
    parsed = json.loads(json.dumps(raw,default=asdict))
    args = [N,source,cap,bound]
    assert verify_result(*args,parsed,learner)
    return args,parsed,learner


def reject(args, result, learner):
    try:
        verify_result(*args,result,learner)
    except ValueError:
        return
    raise AssertionError("tampered certificate accepted")


def changed(data, path, value):
    out = deepcopy(data)
    obj = out
    for key in path[:-1]:
        obj = obj[key]
    obj[path[-1]] = value
    return out


def main():
    cases = [
        verifier(SOURCE,2,majority),
        verifier(ZERO,2,majority),
        verifier(SOURCE,4,lambda h,q: 0 if not h else int(q==SOURCE)
                 if len(h)==1 else majority(h,q)),
    ]
    assert [r["status"] for _,r,_ in cases] == ["witness","unsat","fault"]
    for args, r, learner in cases:
        for key in ("n","S","bound"):
            reject(args,changed(r,[key],r[key]+1),learner)
        reject(args,changed(r,["F",1],-2),learner)
        reject(args,changed(r,["history",0,1],False),learner)
        reject(args,changed(r,["history",0,0],[[],0]),learner)
        reject(args,r,lambda n,s,h,q: 1)
        for i in (0,2,3):
            other = list(args)
            other[i] += 1
            reject(other,r,learner)
        reject([N,((),-2),*args[2:]],r,learner)
    args, r, learner = cases[0]
    reject(args,changed(r,["assignment"],3),learner)
    reject(args,changed(r,["assignment"],4),learner)
    args, r, learner = cases[1]
    reject(args,changed(r,["history"],r["history"][:-1]),learner)
    args, r, learner = cases[2]
    chain, index = r["certificate"]
    for path, value in [
        (["assignment"],0),
        (["certificate",1],len(chain["steps"])),
        (["certificate",0,"roots",0],-1),
        (["certificate",0,"steps",index,"rule"],"invented"),
        (["certificate",0,"steps",index,"context"],chain["roots"][index]),
        (["left"],r["right"]),
        (["right_bit"],1),
    ]:
        reject(args,changed(r,path,value),learner)


if __name__ == "__main__":
    main()
