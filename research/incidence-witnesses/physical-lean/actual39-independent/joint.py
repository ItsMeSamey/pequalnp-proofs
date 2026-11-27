from line_inventory import *
import os,sys
pointlogs=d/'ledger.json';linelogs=d/'line-ledger.json'
for _ in range(3):
 L=json.loads(linelogs.read_text()) if linelogs.exists() else {}
 A=json.loads(pointlogs.read_text())
 done=set(A)|set(L)|{n for n in mods if groups[n]=='prior'}|set(known)
 def miss(n):
  todo=list(new[n]['imports'] if n in new else mods[n]['imports']);seen=set()
  while todo:
   x=todo.pop()
   if x in seen:continue
   seen.add(x)
   if x in mods:
    if x not in done:return True
    todo+=mods[x]['imports']
   elif x in new:
    if x not in done:return True
    todo+=new[x]['imports']
  return False
 wanted=set()
 def urgency(n):
  if n in wanted:return
  wanted.add(n)
  for j in mods.get(n,{}).get('imports',[]):
   if j in mods:urgency(j)
 for x in new:
  if x not in done:urgency(x)
 order=[*new,*[n for n in mods if groups[n]=='new' and n in wanted],*[n for n in mods if groups[n]=='new' and n not in wanted]]
 n=next((n for n in order if n not in done and not miss(n)),None)
 if not n:break
 runner='replay.py' if n in new else 'line_replay.py'
 subprocess.run([sys.executable,str(d/runner)],env=os.environ|dict(REVIEW_BATCH='1',REVIEW_TARGET=n),check=True)
