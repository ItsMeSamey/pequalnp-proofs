"""Reject malformed XOR implementations before evaluating Python indices."""
from copy import deepcopy
import json
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(root))
from check import verify_upper

base=root/'applications'/'xor2'
m=json.loads((base/'application.json').read_text())
care=dict(json.loads((base/'care.json').read_text())['care'])
verify_upper(m,care)

def rejects(key,value):
    fixture=deepcopy(m)
    fixture['upper_bound'][key]=value
    try:
        verify_upper(fixture,care)
    except ValueError:
        return
    raise ValueError('accepted malformed XOR upper bound',key,value)

for index in (-1,True,False,6,999,2.0,'5',None):
    rejects('output',index)
for n in (True,False,0,-1,1,3,2.0):
    rejects('positive_input_count',n)
for gate in (None,{},[],['and'],['or',0],['not',0,1],['xor',0,1],
             [True,0,1],['and',False,1],['and',0,True],['and',0,1.0],
             ['or',-1,1],['or',2,0],['or',999,0],['not','1']):
    gates=deepcopy(m['upper_bound']['gates'])
    gates[0]=gate
    rejects('gates',gates)
rejects('gates',None)
rejects('gates',[])
rejects('output',1)
print('XOR upper witness passed; malformed counts, outputs, gates and pins rejected.')
