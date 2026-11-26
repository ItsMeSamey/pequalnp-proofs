"""Rebuild the chronological catalogs from the proof's successive cut tables."""
from pathlib import Path
import argparse
from three_templates import templates,minimum_unions

def rows(path):
    return [list(map(int,row.split())) for row in path.read_text().splitlines()]

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('stage',choices=['affordable','live','filtered'])
    p.add_argument('input',type=Path,nargs='?')
    a=p.parse_args()
    if a.stage=='affordable':
        for i,t in enumerate(templates()):
            if minimum_unions(t)<=5:print(i,*t)
    elif a.stage=='live':
        for i,x,y,z,count,orbits in rows(a.input):
            c=minimum_unions([x,y,z])
            if x.bit_count()<=3 and count and c<=3:print(i,x,y,z,c)
    else:
        valid={r[0] for r in rows(a.input/'hard.tsv') if r[-1]}
        for r in rows(a.input/'live.tsv'):
            if r[0] in valid:print(*r)
