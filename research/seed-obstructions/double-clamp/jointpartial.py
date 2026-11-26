from pathlib import Path
s=Path('jointall.py').read_text().replace("open('jointgood','w')","open('jointpartial','w')").replace("if all(A&h for h in hit):print(s,r,A,file=out)","print(s,r,A,sum(1<<p for p,h in enumerate(hit) if A&h),file=out)")
exec(s)
