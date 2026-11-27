from pathlib import Path
import json,subprocess,tempfile
p=Path('/workspace/scratch/site-team-11')
with tempfile.TemporaryDirectory() as d:
 q=Path(d)
 s=(p/'cut199-left-bank-cotree.cjs').read_text().replace('if(n!==6)','if(n!==5)').replace("let sig=ws.filter((_,i)=>m>>i&1).sort((a,b)=>a-b),k=sig.join(',');","let base=ws.filter((_,i)=>m>>i&1);for(let extra of base){let sig=[...base,extra].sort((a,b)=>a-b),k=sig.join(',');").replace('hits.set(k,d)}','hits.set(k,d)}}').replace('for(let k=lo;k<hi;k++)visit([...raw,first[k]],1);','visit(raw,0);')
 (q/'cotree.cjs').write_text(s)
 v=json.loads(subprocess.check_output(['node',q/'cotree.cjs','0','20','3']))
 print('distinct5+alias cotree tested',v['order'],'survive',len(v['hits']))
 (q/'cut199-left-bank-cotree-survivors.json').write_text(json.dumps(v))
 for f,args in [('cut199-left-general-parity.cjs',['cut199-left-general-parity.json']),('cut199-parity-full.cjs',[])]:
  (q/f).write_bytes((p/f).read_bytes());r=subprocess.run(['node',f,*args],cwd=q,check=True,capture_output=True,text=True);print(r.stdout[:400])
 print('final alias',len(json.loads((q/'cut199-parity-full.json').read_text())))
