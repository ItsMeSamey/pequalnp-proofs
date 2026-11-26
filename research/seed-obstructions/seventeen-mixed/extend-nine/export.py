from pathlib import Path
def export_indexed(families,bases,dest):
    index={tuple(map(int,l.split())):i for i,l in enumerate(Path(bases).read_text().splitlines(),1)}
    with Path(families).open() as src,Path(dest).open('w') as out:
        for line in src:
            *base,mask,lower=map(int,line.split())
            assert len(base)==9
            print(index[tuple(base)],mask,lower,file=out)
