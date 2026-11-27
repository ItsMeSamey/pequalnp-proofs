from pathlib import Path as P
import re,json,hashlib,subprocess
d=P(__file__).resolve().parent;w=P((d/'workdir').read_text().strip())
p=P('/workspace/pequalnp-proofs'); rel='lean/PEqualNP/Outside/L_meta_2794.lean'
commit=subprocess.check_output(['git','-C',p,'rev-parse','HEAD'],text=True).strip()
text=(p/rel).read_text()
generic=text.split('theorem PEqualNP.Outside.L_meta_2794 : ',1)[1].split(' := by',1)[0]
inst=re.sub(r'\bx1\b','(401 : ℕ)',generic.replace('(x1 x2 : ℕ)','(x2 : ℕ)',1))
wrapper=(w/'IncidenceOfficial401Type.lean').read_text().split('theorem posted_type_exact (h : ScalarLower401) : ',1)[1].split(' := posted_401 h',1)[0]
assert wrapper==inst
(d/'official-compare.json').write_text(json.dumps(dict(worktree_head=commit,official_file_source='local posted problem copy',official_file=rel,official_sha256=hashlib.sha256(text.encode()).hexdigest(),specialized_type_sha256=hashlib.sha256(inst.encode()).hexdigest(),explicit_premise='ScalarLower401'),indent=2)+'\n')
