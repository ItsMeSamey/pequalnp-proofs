"""Read emitted Lean literals directly and replay all cells in parallel as integers."""
import ast
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent
text = (root/'Enriched30Data.lean').read_text()
def table(name):
    return ast.literal_eval(re.search(r'^def '+name+r' : List .*? := (\[.*?\])',text,re.M|re.S)[1])
def require(ok, label):
    if not ok:
        raise ValueError(label)

raw = json.loads((root/'source-circuit.json').read_text())['net']
gates = [(op,ast.literal_eval(args)) for op,args in re.findall(r'⟨\.(and|or|not), (\[[0-9, ]*\])⟩', text)]
require(gates==[(g['op'],g['inputs']) for g in raw['gates']] and len(gates)==170,'gate list')
output = int(re.search(r'output := (\d+)',text)[1])
require(output==raw['output'],'output')
rows = [int(x,16) for x in re.findall(r'0x[\da-fA-F]+',(root/'issued-statement.txt').read_text())]
require(len(rows)==32 and table('rows')==rows,'issued matrix')
expected = sum(row<<(32*i) for i,row in enumerate(rows))
full = (1<<1024)-1
wires = [((1<<32)-1)<<(32*r) for r in range(32)] + [sum(1<<(32*r+c) for r in range(32)) for c in range(32)]
for op,pins in gates:
    a,b = wires[pins[0]],wires[pins[-1]]
    wires.append({'not':full^a,'and':a&b,'or':a|b}[op])
require((wires[output]^expected).bit_count()==14,'source mismatch count')
bank,essential,binate = map(table,('bank','essential','binate'))
support = json.loads((root/'support.json').read_text())
require(bank==support['bank'] and len(set(bank))==len(bank)==30,'bank')
require(len(essential)==28 and {w for w,*_ in essential}==set(bank)-{90,137},'mandatory IDs')
require(len(binate)==11 and {w for w,*_ in binate}=={89,101,125,130,136,163,170,189,193,207,214},'binate IDs')
def edge(w,a,b):
    require(0<=a<1024 and 0<=b<1024,'cell bounds')
    require({j for j in bank if (wires[j]>>a ^ wires[j]>>b)&1}=={w},'singleton')
    require((wires[w]>>a)&1==0,'physical orientation')
    labels = ((expected>>a)&1,(expected>>b)&1)
    require(labels[0]!=labels[1],'graph labels')
    return labels
for w,a,b in essential:
    edge(w,a,b)
for w,a,b,c,d in binate:
    require(edge(w,a,b)==(0,1) and edge(w,c,d)==(1,0),'both signs')
print('Verified 1024 cells, 170 gates, 14 source discrepancies, 28 essential and 11 binate donors.')
