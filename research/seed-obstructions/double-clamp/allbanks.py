from pathlib import Path
s=Path('prep.py').read_text().replace("if any(not any(n&stars[i]&~bad and n&stars[j]&~bad for n in ok) for i,j in combinations(range(7),2)):continue","").replace("open('banks','w')","open('allbanks','w')")
exec(s)
