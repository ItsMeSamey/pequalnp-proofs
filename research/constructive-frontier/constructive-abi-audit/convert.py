"""Validate graph-circuit ABI and invoke the frozen frontier converter."""
import argparse
import json
from pathlib import Path
import sys

frozen = Path(__file__).resolve().parents[1] / "cut199-control-pair"
sys.path.insert(0, str(frozen))
from constructive_frontier import convert as frozen_convert


def convert(candidate, n=None):
    if not isinstance(candidate, dict):
        raise ValueError("expected graph circuit object")
    if not all(key in candidate for key in ("edges", "gates", "output")):
        raise ValueError("expected edges, gates and a designated output; materialize tap banks first")
    declared = candidate.get("n")
    if n is not None and "n" in candidate and n != declared:
        raise ValueError("n disagrees with explicit input count")
    count = declared if n is None else n
    if type(count) is not int or count < 1:
        raise ValueError("supply a positive input count with n or --n")
    edges, gates, out = (candidate[k] for k in ("edges","gates","output"))
    if not isinstance(edges,list) or not edges:
        raise ValueError("expected a nonempty simple graph edge list")
    if not isinstance(gates,list) or type(out) is not int or not 0 <= out < count+len(gates):
        raise ValueError("designated output must name an input or a listed gate")
    return frozen_convert(dict(candidate,n=count))


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate",type=Path)
    parser.add_argument("--n",type=int)
    parser.add_argument("-o","--output",type=Path)
    args=parser.parse_args()
    try:
        result=convert(json.loads(args.candidate.read_text()),args.n)
    except (ValueError,KeyError,TypeError,IndexError) as exc:
        parser.exit(2,f"invalid circuit: {exc}\n")
    payload=json.dumps(result,indent=2)+"\n"
    if args.output: args.output.write_text(payload)
    else: print(payload,end="")
