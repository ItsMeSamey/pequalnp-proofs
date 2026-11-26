from pathlib import Path
import subprocess
key=lambda line:tuple(map(int,line.split()[1:4]))
record=Path('negative.log')
seen={key(x) for x in record.read_text().splitlines()}
with record.open('a') as stream:
    for line in Path('keys.tsv').read_text().splitlines():
        job=tuple(map(int,line.split()))
        if job in seen: continue
        ans=subprocess.check_output(['/dev/shm/register25','7879121',*map(str,job)],text=True)
        assert key(ans)==job and ' UNSAT ' in ans
        stream.write(ans);stream.flush()
