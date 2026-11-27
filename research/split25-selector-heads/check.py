"""Replay the fixed prefix and verify same-orientation literal-selector bounds."""
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
FULL = (1 << 1024) - 1


def require(ok, why):
    if not ok:
        raise ValueError(why)


def load(name):
    return json.loads((ROOT / name).read_bytes())


def check_inputs():
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ')
        require(sha256((ROOT / name).read_bytes()).hexdigest() == digest, name)


def replay():
    public = load('public-task.json')
    require(public['gap']['id'] == 'L-meta-20579' and public['shard'] == 53, 'task')
    rows = [int(s,16) for s in re.findall(r'0x[0-9a-fA-F]+', public['gap']['statement'])]
    manifest = load('prefix115.json')
    require(len(rows) == 32 and rows == manifest['rows'], 'target rows')
    require(all(0 <= x < 2**32 for x in rows), 'target row width')
    rowbytes = b''.join(x.to_bytes(4,'little') for x in rows)
    require(sha256(rowbytes).hexdigest() == manifest['graph_sha256'], 'graph hash')
    require(manifest['problem'] == 'L-meta-20579' and manifest['shard'] == 53, 'prefix task')
    wires = [((1 << 32) - 1) << (32*r) for r in range(32)]
    wires += [sum(1 << (32*r+c) for r in range(32)) for c in range(32)]
    gates = manifest['prefix_gates']
    require(len(gates) == 115, 'prefix size')
    marker = None
    for number, gate in enumerate(gates,64):
        op, args = gate['op'], gate['inputs']
        require(op in ('and','or','not') and len(args) == (1 if op == 'not' else 2),
                'gate operation and arity')
        require(all(type(w) is int and 0 <= w < number for w in args), 'gate inputs')
        a = wires[args[0]]
        if op == 'not':
            value = FULL ^ a
            if marker is None and args[0] >= 64:
                marker = number
        elif op == 'or':
            value = a | wires[args[1]]
        else:
            value = a & wires[args[1]]
        wires.append(value)
    require(marker is not None and marker == manifest['physical_marker_wire'], 'first internal NOT')
    require(sum(((wires[marker] >> (33*k)) & 1) << k for k in range(6)) == 53, 'NOT mask')
    ports = manifest['port_physical_wires']
    require(len(set(ports)) == len(ports) == 25 and all(0 <= w < len(wires) for w in ports),
            'physical port list')
    physical = dict(zip(manifest['closure_source_wires'],range(64,179),strict=True))
    require([physical.get(w,w) for w in manifest['port_source_wires']] == ports, 'port mapping')
    cells = []
    for i in range(1024):
        r,c = divmod(i,32)
        value = sum(((wires[w] >> i) & 1) << j for j,w in enumerate(ports))
        cells.append([i,(rows[r] >> c) & 1,value])
    require(cells == manifest['care'], 'reconstructed cells')
    words = [{s for _,y,s in cells if y == label} for label in (0,1)]
    require([len(group) for group in words] == [573,399] and not words[0] & words[1],
            'signature classes')
    for group in words:
        for j in range(25):
            require({(w >> j) & 1 for w in group} == {0,1}, 'old unit literal can separate class')
    return cells,manifest


def packed_cells(pack, label, cells, manifest):
    require(pack['source_sha256'] == manifest['source_sha256'] and
            pack['basis_wire_ids'] == manifest['port_source_wires'], 'packing source/bank')
    key, blocker = ('positive_cells','negative_cells_lex') if label else ('negative_cells','positive_cells_lex')
    points = pack[key]
    require(len(points) == (50 if label else 34) and
            len({cells[i][2] for i in points}) == len(points), 'packing size and distinct signatures')
    require(all(0 <= i < 1024 and cells[i][1] == label for i in points), 'packing label')
    for (i,j), z in zip(combinations(points,2),pack[blocker],strict=True):
        require(0 <= z < 1024 and cells[z][1] != label, 'blocker label')
        a,b,t = (cells[n][2] for n in (i,j,z))
        require(((t ^ a) & ~(a ^ b)) == 0, 'blocker disagrees on shared coordinate')
    return points


def main():
    from branch import branch_bound
    check_inputs()
    cells, manifest = replay()
    cube = load('signed-cube-pack.json')
    clause = load('signed-clause-pack.json')
    positives_pack = packed_cells(cube, 1, cells, manifest)
    negatives = packed_cells(clause, 0, cells, manifest)
    decreasing = set()
    for coordinate, p, n in cube['negative_literal_edges']:
        require(0 <= coordinate < 25 and 0 <= p < 1024 and 0 <= n < 1024, 'edge domain')
        a, b = cells[p], cells[n]
        require(a[1] == 1 and b[1] == 0 and not (a[2] >> coordinate & 1)
                and a[2] ^ b[2] == 1 << coordinate, 'decreasing direction')
        decreasing.add(coordinate)
    require(len(decreasing) == 18, 'distinct negations')

    min_cnf, min_dnf = 1000, 1000
    mixed = []
    summaries = []
    for selector in range(25):
        local = {}
        for side in (0, 1):
            branch = [row for row in cells if (row[2] >> selector & 1) == side]
            positives = [x for _, label, x in branch if label]
            for form, pack in [("CNF", negatives), ("DNF", positives_pack)]:
                head = branch_bound(branch, pack, form)
                require("joins" in head, "constant branch")
                local[side, form] = head
            require(positives, 'empty positive slice')
            for coordinate in range(25):
                for sign in (0, 1):
                    if all((x >> coordinate & 1) == sign for x in positives):
                        require(all((cells[i][2] >> coordinate & 1) == sign
                                    for i in negatives if (cells[i][2] >> selector & 1) == side),
                                'valid branch unit rejects packed negative')
        mandatory = len(decreasing - {selector})
        min_cnf = min(min_cnf, 34 + 32 + mandatory)
        cube_units = sum(len(local[side,'DNF']['packed_unit_coverage']) for side in (0,1))
        require(cube_units <= 2, 'packed DNF unit coverage')
        dnf_bound = 48 + (50 - cube_units) + mandatory
        min_dnf = min(min_dnf, dnf_bound)
        summaries.append(dict(port=selector, wire=manifest['port_source_wires'][selector],
                              cnf=66+mandatory, dnf=dnf_bound,
                              dnf_units=[local[s,'DNF']['units'] for s in (0,1)]))
        for first, second in [('CNF','DNF'), ('DNF','CNF')]:
            pair = [local[0, first], local[1, second]]
            coords = {j for head in pair for j, _, _ in head['decreasing_edges']}
            roots = [head['nonunits'] for head in pair]
            joint = sum(r + max(0, r-1) for r in roots) + len(coords)
            lower = max(joint, *(head['lower'] for head in pair))
            mixed.append(dict(port=selector, wire=manifest['port_source_wires'][selector],
                              zero=first, one=second, nonunits=roots,
                              negative_coordinates=sorted(coords), joint=joint, lower=lower,
                              heads=pair))
    mixed_min = min(r['lower'] for r in mixed)
    require(min_cnf == 83 and min_dnf >= 113 and mixed_min >= 76, 'selector lower bounds')
    result = dict(cnf=min_cnf, dnf=min_dnf, mixed=mixed_min, same_cases=summaries, mixed_cases=mixed)
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--report', type=Path)
    output = parser.parse_args().report
    if output:
        output.write_text(json.dumps(result, indent=1) + '\n')
    print('25 selectors, 50 mixed orientations, 1786 pair blockers')
    for label, bound in [('cnf', min_cnf), ('dnf', min_dnf)]:
        print(label, bound, [(r['port'], r['wire']) for r in summaries if r[label] == bound])
    print('mixed', mixed_min, [(r['port'], r['wire'], r['zero'], r['one'])
                               for r in mixed if r['lower'] == mixed_min])


if __name__ == '__main__':
    main()
