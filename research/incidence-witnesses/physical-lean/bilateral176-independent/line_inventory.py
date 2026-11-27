from inventory import *
import io,subprocess,zipfile
d=P(__file__).resolve().parent
ref='43a0b625638dab5f2fe9dc1646561c1fe75f851d:research/incidence-witnesses/physical-lean/line-freeze/bilateral-actual-9843.zip'
data=subprocess.check_output(['git','-C','/workspace/pnp-research','show',ref]);assert hashlib.sha256(data).hexdigest()=='6a6c61561d249c861cd9644c4e6162004682d5746e41c6ef38be13f71548692c'
z=zipfile.ZipFile(io.BytesIO(data));mods=json.loads(z.read('manifest.json'))['modules'];a=json.loads((d/'frozen.json').read_text()); groups={}
for n,r in mods.items():
 k=n.replace('.','/');assert hashlib.sha256(z.read('src/'+k+'.lean')).hexdigest()==r['src']
 groups[n]='prior' if k in known and sha(P(known[k]))==r['object'] else 'actual39' if n in a and a[n]['source']==r['src'] and a[n]['object']==r['object'] else 'new'
 assert r['log'] is None or hashlib.sha256(z.read(r['log_path'])).hexdigest()==r['log']
if __name__=='__main__':print({k:list(groups.values()).count(k) for k in set(groups.values())})
