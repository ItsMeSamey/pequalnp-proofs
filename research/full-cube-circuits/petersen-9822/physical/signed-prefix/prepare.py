from pathlib import Path
import re
p=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_9825.lean')
ls=p.read_text().splitlines(True)
starts=[j for j in range(5,1250) if re.match('^(?:private |noncomputable )?(?:lemma|theorem|inductive|def|abbrev) ',ls[j])]
cuts=[4]+[next(j for j in starts if j>=i) for i in [140,284,417,545,680,810,942,1080,1197]]
for i,(a,b) in enumerate(zip(cuts,cuts[1:])):
 imp='import '+(f'Prefix{i-1}' if i else 'PEqualNP.Defs')+'\n'
 body=re.sub('^private lemma ','lemma ',''.join(ls[a:b]),flags=re.M)
 Path(f'Prefix{i}.lean').write_text(imp+''.join(ls[1:4])+body+'\nend Engine\nend PEqualNP.Outside.L_meta_9825\n')
Path('Trial.lean').write_text(Path('../Signed9822Core.lean').read_text().replace('import PEqualNP.Outside.L_meta_9825',f'import Prefix{i}'))
with Path('Trial.lean').open('a') as final:
 final.write('#print axioms Research.Signed9822.binaryFloorOfFace\n#print axioms Research.Signed9822.notBudgetOfFace\n')
Path('stage.py').write_text(Path('../../floor16/stage.py').read_text())
