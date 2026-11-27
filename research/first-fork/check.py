"""Replay the fixed donor-bank certificate with Python's standard library."""
import hashlib
import json
import re
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
BANK = [42, 65, 83, 86, 90, 94, 95, 99, 101, 102, 107, 110, 115, 165, 186]
PORTS = [213, 222, 225]
ALL = (1 << 1024) - 1


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def load(name):
    return json.loads((HERE / name).read_bytes())


def evaluate(control, overrides):
    wires = [((1 << 32) - 1) << (32 * row) for row in range(32)]
    wires += [sum(1 << (32 * row + col) for row in range(32)) for col in range(32)]
    for gate in control['gates']:
        pins = gate['inputs']
        require(len(pins) <= 2 and all(type(p) is int and p >= 0 for p in pins), 'invalid pins')
        values = [wires[p] if p < len(wires) else 0 for p in pins]
        op = gate['op']
        if op == 'or':
            val = 0
            for arg in values:
                val |= arg
        elif op == 'and':
            val = ALL
            for arg in values:
                val &= arg
        elif op == 'not':
            val = ALL ^ (values[0] if values else 0)
        else:
            raise ValueError(op)
        wires.append(overrides.get(len(wires), val))
    return wires


def check():
    control = load('control.json')
    unit = load('unit.json')
    wedge = load('wedges.json')
    ess = load('essential.json')
    require(hashlib.sha256((HERE / 'control.json').read_bytes()).hexdigest()
            == 'f6a081e8e9bb9430fc2af1272a2b8d695fb2fb43440c5897d351ffa580693055', 'control identity')
    require(hashlib.sha256(unit['gap']['statement'].encode()).hexdigest()
            == 'f5d5f09a84757c4595df9a50b659e4862f92b371662d4e460ddb777d926f2a22', 'unit statement identity')
    require(wedge['bank'] == ess['bank'] == BANK and wedge['outputs'] == ess['outputs'] == PORTS, 'cut')
    rows = [int(s, 16) for s in re.findall(r'0x[0-9a-fA-F]+', unit['gap']['statement'])]
    require(len(rows) == 32 and all(r < 1 << 32 for r in rows), 'target dimensions')
    target = sum(r << (32 * i) for i, r in enumerate(rows))
    wires = evaluate(control, {})
    require(len(control['gates']) == 181 and wires[control['output']] == target, 'control size/truth')
    first = next(i for i, g in enumerate(control['gates'], 64)
                 if g['op'] == 'not' and g['inputs'] and 64 <= g['inputs'][0] < i)
    route = sum(((wires[first] >> (33*k)) & 1) << k for k in range(6))
    require(route == 0x35, 'control route')
    downstream = [evaluate(control, {p: ALL if tag >> j & 1 else 0
                                    for j, p in enumerate(PORTS)})[control['output']] for tag in range(8)]
    cells = {}
    groups = {}
    for i in range(1024):
        sig = ''.join(str((wires[w] >> i) & 1) for w in BANK)
        mask = sum((1 << k) for k, val in enumerate(downstream) if ((val ^ target) >> i) & 1 == 0)
        require(mask in (1, 254, 255), 'context does not depend only on port OR')
        cells[divmod(i,32)] = (sig, mask)
        groups[sig] = groups.get(sig, 255) & mask
    require(0 not in groups.values(), 'bank inconsistent')
    forced = {s: int(mask == 254) for s, mask in groups.items() if mask in (1, 254)}

    def flip(sig, pos):
        return sig[:pos] + ('0' if sig[pos] == '1' else '1') + sig[pos+1:]

    def cited(obs):
        sig, mask = cells[tuple(obs['cell'])]
        require(sig == obs['signature'] and mask in (1,254) and int(mask == 254) == obs['value'],
                'wedge cell does not force stated value')
        return sig, forced[sig]

    detected = set()
    positives_and = set()
    positives_or = set()
    for i,j in combinations(range(len(BANK)),2):
        pair = BANK[i], BANK[j]
        centers = set()
        for s,v in forced.items():
            x,y = flip(s,i), flip(s,j)
            if forced.get(x) == forced.get(y) == 1-v:
                centers.add((s[i],s[j]))
                if forced.get(flip(x,j)) == 1-v:
                    if (s[i],s[j],v) == ('1','1',1):
                        positives_and.add(pair)
                    if (s[i],s[j],v) == ('0','0',0):
                        positives_or.add(pair)
        if len(centers) >= 2:
            detected.add(pair)
    require((len(positives_and),len(positives_or),len(positives_and & positives_or)) == (33,2,0),
            'strict square counts')
    edges = set()
    for edge in wedge['edges']:
        pair = tuple(edge['donors'])
        i,j = map(BANK.index,pair)
        corners = set()
        for w in edge['wedges']:
            s,v = cited(w['center'])
            require(cited(w['flip_first']) == (flip(s,i),1-v), 'first neighbor')
            require(cited(w['flip_second']) == (flip(s,j),1-v), 'second neighbor')
            require(w['corner'] == s[i]+s[j], 'corner')
            corners.add(w['corner'])
        require(len(corners)>=2 and pair not in edges,'edge witnesses')
        edges.add(pair)
    require(edges == detected and len(edges)==14, 'exact wedge edges')
    tri = wedge['triangle']
    require(tri == [65,102,107] and set(combinations(tri,2)) <= edges, 'triangle')
    colors = wedge['three_coloring']
    require(len(colors) == 3 and sorted(v for c in colors for v in c) == BANK,'color partition')
    require(all(not any(a in c and b in c for c in colors) for a,b in edges),'improper coloring')
    seen = []
    for e in ess['certificates']:
        d = e['donor']
        x,y = e['x'],e['y']
        require(flip(x,BANK.index(d)) == y,'necessity signatures')
        masks = e['allowed']
        require(sorted(masks)==[1,254],'necessity values')
        for sig, mask, cell in zip((x,y),masks,e['cells'],strict=True):
            require(cells[tuple(cell)]==(sig,mask) and groups[sig]==mask,'necessity cell')
        seen.append(d)
    require(sorted(seen)==BANK,'necessary donors')
    print(f'181 gates; route {route:02x}; 1024 cells × 8 tuples; {len(groups)} groups; '
          '105 pairs; strict AND/OR/both 33/2/0; 14 wedge edges; chromatic number 3; 15 necessary donors.')


if __name__ == '__main__':
    check()
