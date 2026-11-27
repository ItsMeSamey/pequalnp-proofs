"""Reconstruct all physical cells from the public target and frozen circuit prefix."""
from hashlib import sha256
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
