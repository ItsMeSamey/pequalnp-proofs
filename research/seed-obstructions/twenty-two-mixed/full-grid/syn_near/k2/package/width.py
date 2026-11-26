from pathlib import Path
exec(Path(__file__).with_name('independent.py').read_text().split('step=int')[0])
cases=[(e,9,4) for e in (15,23,27,46,83)]+[(e,8,1) for e in (7,13,14,19,81)]
for e,b,cost in cases:
 result,assignment=model(e,b,0,30000,cost)
 print(e,b,cost,result,assignment,flush=True)
 if result!='UNSAT':
  raise AssertionError((e,b,cost,result))
