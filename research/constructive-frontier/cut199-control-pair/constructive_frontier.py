"""Return a shorter graph circuit or an equal-size TopForm circuit of defect D+k."""
from frontiers import measure
from check4186 import check


def trim(n, gates, out):
    live = {out}
    for i in reversed(range(len(gates))):
        if n+i in live:
            live.update(gates[i][1:])
    mapping = {i:i for i in range(n)}
    compact = []
    for i,(op,a,b) in enumerate(gates,n):
        if i in live:
            mapping[i] = n+len(compact)
            compact.append([op,mapping[a],mapping[b]])
    return compact,mapping[out]


def extract(n, gates, out, selected):
    # Preserve the original selected cone; append only materially changed residual gates.
    all_gates = list(gates)
    residual = list(range(n))
    for i,(op,a,b) in enumerate(gates,n):
        x,y = residual[a],residual[b]
        if i == selected:
            wire = None
        elif x is None or y is None:
            wire = (y if x is None else x) if op == 'or' else None
        elif (x,y) == (a,b):
            wire = i
        else:
            wire = n+len(all_gates)
            all_gates.append([op,x,y])
        residual.append(wire)
    new_out = selected
    if residual[out] is not None and residual[out] != selected:
        new_out = n+len(all_gates)
        all_gates.append(['or',selected,residual[out]])
    return trim(n,all_gates,new_out)


def normalize(n, edges, gates, out):
    original_size = len(gates)
    gates,out = trim(n,gates,out)
    steps = []
    while len(gates) == original_size:
        data = dict(n=n,edges=edges,gates=gates,output=out)
        audit = check(n,edges,gates,out)
        if not audit['computes']:
            raise ValueError('input must compute the graph edge function')
        if audit['topForm']:
            break
        f = measure(data)['frontiers']
        ands = set(audit['tops']+audit['junk'])
        buried = [i for i in audit['belowF'] if any(i in audit['inCone'][j] for j in ands)]
        selected = next((i for i in buried if
                         sum(n+i in g[1:] for g in gates)>1 or
                         any(n+i in gates[j][1:] for j in ands)),None)
        if selected is None:
            selected = f[0]['clean_input_gates'][0]
        steps.append(selected+n)
        gates,out = extract(n,gates,out,selected+n)
    return dict(n=n,edges=edges,gates=gates,output=out),steps


def convert(candidate):
    """Return a canonical graph circuit, evidence for the branch and a step trace."""
    from frontiers import measure
    raw = candidate["gates"]
    gates = []
    for g in raw:
        if isinstance(g, dict):
            op = g["op"]
            a,b = g["inputs"]
        else:
            op,a,b = g
        gates.append(["and" if op is True else "or" if op is False else op,a,b])
    n = candidate["n"]
    edges = candidate["edges"]
    start = dict(n=n,edges=edges,gates=gates,output=candidate["output"])
    before = measure(start)
    if not before["computes"]:
        raise ValueError("input circuit does not compute the given graph function")
    out,steps = normalize(n,edges,gates,start["output"])
    after = measure(out)
    sizes = [len(gates),len(out["gates"])]
    branch = "shorter" if sizes[1] < sizes[0] else "equal-size-topform"
    if not after["computes"] or (branch == "equal-size-topform" and not (
            sizes[0] == sizes[1] and after["topForm"] and after["D"] == before["D_plus_k"])):
        raise AssertionError("constructive dichotomy failed")
    return dict(branch=branch,sizes=sizes,selected_wires=steps,before=before,after=after,circuit=out)


if __name__ == "__main__":
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input",type=Path,help="circuit JSON with n, edges, gates, output")
    parser.add_argument("-o","--output",type=Path,help="write result JSON (default stdout)")
    args = parser.parse_args()
    result = json.dumps(convert(json.loads(args.input.read_text())),indent=2)+"\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result,end="")
