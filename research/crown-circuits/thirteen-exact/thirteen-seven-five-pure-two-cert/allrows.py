from pathlib import Path
rows=[list(map(int,x.split())) for x in Path('strong.tsv').read_text().splitlines()]
seen={}
for i,r in enumerate(rows):seen.setdefault(tuple(r[:22]+r[25:]),[]).append(i)
Path('allrows.tsv').write_text(''.join(' '.join(map(str,rows[v[0]]))+'\n' for v in seen.values()))
Path('allrows.ids').write_text(''.join(' '.join(map(str,v))+'\n' for v in seen.values()))
print(len(rows),len(seen))
