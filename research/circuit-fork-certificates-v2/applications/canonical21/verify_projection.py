"""Replay the frozen one-hot graph and recover the projected 21-bit care table."""
from pathlib import Path
import hashlib
import json
import re
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent / "shared"))

from interface import reconstruct, require

here = Path(__file__).resolve().parent
read = lambda name: json.loads((here/name).read_text())
shared = here.parent/'shared'
src = (shared/'control.lean').read_bytes()
require(hashlib.sha256(src).hexdigest() == '08b07ebb1edfb826bb061afcc09558ae5d75a6d4d626e43c373c4d8e6855d731', 'wrong control')
rows = [int(s, 16) for s in json.loads((shared/'graph.json').read_text())]
context = json.loads((shared/'context.json').read_text())
require(rows == [int(s, 16) for s in re.findall(rb'0x([0-9a-fA-F]+)',src)], 'row words')
require(context['gates'] == [list(map(int,g)) for g in re.findall(rb'\((\d+),(\d+),(\d+)\)',src)], 'gate codes')
positive, negative = reconstruct(context, rows)
p = read('paid26-alias-ac6.json')
bank = context['bank'] + [244, 1000000]
require(bank == p['original_bank_slot_to_wire'], 'donor order')
ops = [(0,153,244),(1,85,121),(1,23,68),(1,60,212),(1,50,81),(1,31,49)]
require([[o,bank.index(a),bank.index(b)] for o,a,b in ops] == p['gate_code_0_and_1_or'], 'six gates')
retained = [24,63,74,86,88,99,106,109,112,131,134,136,141,154,208]
require([bank.index(w) for w in retained]+list(range(28,34)) == p['projected_slot_to_extended_slot'], 'projected order')
labels = {}
for label, patterns in enumerate([negative,positive]):
    for pattern in patterns:
        wires = {w:(pattern >> i)&1 for i,w in enumerate(context['bank'])}
        wires[244] = 1-wires[121]
        extra = [(wires[a]&wires[b]) if o==0 else (wires[a]|wires[b]) for o,a,b in ops]
        key = sum(v<<j for j,v in enumerate([wires[w] for w in retained]+extra))
        require(labels.setdefault(key,label)==label,'projection conflict')
require(len(labels)==469 and sum(labels.values())==84, 'projected counts')
require(sorted(labels.items()) == sorted(map(tuple,p['care'])), 'stored care table')
print('Verified graph cells 1024, original care vectors 519, projected care vectors 469.')
chain = [1024,17408,17536,17856]
require(all(a != b and a&b == a for a,b in zip(chain,chain[1:])), 'postcone chain order')
require([labels[x] for x in chain] == [0,1,0,1], 'postcone chain labels')
