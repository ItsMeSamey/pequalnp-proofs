from inventory import *
import io,subprocess,zipfile
d=P(__file__).resolve().parent
ref='b41badb879c7f0e0da917e04b45ebc974f061ac0:research/incidence-witnesses/physical-lean/line-freeze/line-actual-3382.zip'
data=subprocess.check_output(['git','-C','/workspace/pnp-research','show',ref]);assert hashlib.sha256(data).hexdigest()=='6d10869dc759364c25f070f7b24c2d17ae0163e0a29d1fdd49095d8de5712d5c'
z=zipfile.ZipFile(io.BytesIO(data));mods=json.loads(z.read('manifest.json'))['modules'];a=json.loads((d/'frozen.json').read_text()); groups={}
for n,r in mods.items():
 k=n.replace('.','/');assert hashlib.sha256(z.read('src/'+k+'.lean')).hexdigest()==r['src']
 groups[n]='prior' if k in known and sha(P(known[k]))==r['object'] else 'actual39' if n in a and a[n]['source']==r['src'] and a[n]['object']==r['object'] else 'new'
 assert r['log'] is None or hashlib.sha256(z.read(r['log_path'])).hexdigest()==r['log']
if __name__=='__main__':print({k:list(groups.values()).count(k) for k in set(groups.values())})
