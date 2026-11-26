"""Recompute the thirteen-input/six-AND census and required source families."""
import argparse
from collections import defaultdict
import gzip
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent

def checked(args,cwd,inp=None,out=None,err=None):
    with (open(inp,'rb') if inp else open('/dev/null','rb')) as f:
        result=subprocess.run([str(s) for s in args],cwd=cwd,stdin=f,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    if out:Path(out).write_bytes(result.stdout)
    if err:Path(err).write_bytes(result.stderr)
    return result.stdout.decode()

def build(name,cwd):
    path=cwd/name
    checked(['c++','-std=c++20','-O3',ROOT/(name+'.cpp'),'-o',path],cwd)
    return path

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--profiles',type=int,nargs='*',help='Replay only these profile IDs after regenerating the census.')
    ap.add_argument('--census-only',action='store_true')
    ap.add_argument('--ordinary',action='store_true',help='Also rerun all three ordinary maximum-width anchors.')
    args=ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp)
        frozen=gzip.decompress((ROOT/'hard.tsv.gz').read_bytes())
        if args.profiles is not None and not args.census_only:
            (tmp/'hard.tsv').write_bytes(frozen)
        else:
            census=checked(['python3',ROOT/'project-three.py',ROOT/'ten-canon.txt.gz'],tmp)
            assert census==(ROOT/'partition-three.log').read_text()
            checked([build('filter',tmp)],tmp,inp=tmp/'projected-three.tsv',out=tmp/'hard.tsv',err=tmp/'screen.log')
            assert (tmp/'screen.log').read_text()==(ROOT/'hard.log').read_text()
            assert (tmp/'hard.tsv').read_bytes()==frozen
            assert checked([build('control',tmp)],tmp)==(ROOT/'positive-control.log').read_text()
            assert checked(['node',ROOT/'positive-anchors.js'],tmp)==(ROOT/'positive-anchors.log').read_text()
            assert checked(['node',ROOT/'bfs-audit.js',tmp/'hard.tsv'],tmp).strip()=='Independently matched protected bases on 9347 hard profiles.'
            print('Census and positive controls verified.',flush=True)
        assert checked(['python3',ROOT/'split.py'],tmp)==(ROOT/'hard-split.log').read_text()
        if args.ordinary:
            exe=build('ordinary13',tmp)
            for width in (4,5,6):
                assert checked([exe,6,width,0,18],tmp)==(ROOT/f'ordinary-{width}.log').read_text()
            print('Ordinary maximum widths 4, 5 and 6 verified.',flush=True)
        if args.census_only:return
        ledger={}
        for line in (ROOT/'ledger.tsv').read_text().splitlines():
            q,i,method,visits,hit=line.split()
            assert int(i) not in ledger and int(hit)==0
            ledger[int(i)]=(int(q),method,int(visits))
        assert len(ledger)==9347
        requested=set(args.profiles) if args.profiles is not None else set(ledger)
        assert requested<=ledger.keys()
        found=set()
        for q in range(2,7):
            groups=defaultdict(list)
            for line in (tmp/f'q{q}.tsv').read_text().splitlines():
                i=int(line.split()[0]);assert ledger[i][0]==q
                if i in requested:
                    groups[ledger[i][1]].append(line);found.add(i)
            for method,inputs in groups.items():
                packed=tmp/f'{q}.{method}.tsv'
                packed.write_text('\n'.join(inputs)+'\n')
                if method=='ordinary':
                    assert len(inputs)==1
                    if not args.ordinary:
                        exe=build('ordinary13',tmp)
                        for width in (4,5,6):
                            assert checked([exe,6,width,0,18],tmp)==(ROOT/f'ordinary-{width}.log').read_text()
                    continue
                program={'signed':'signed13.js','port':'port-anchor.js','group':'group-anchor.js','condition-port':'conditional.js','condition-group':'conditional.js'}[method]
                cmd=['node',ROOT/program]
                if method.startswith('condition-'):cmd.extend([q,packed,method.split('-')[1]])
                else:cmd.append(packed)
                rr=checked(cmd,tmp).splitlines()
                assert len(rr)==len(inputs)
                for line,out in zip(inputs,rr):
                    i,_,v,hit=map(int,out.split())
                    assert int(line.split()[0])==i and ledger[i][2]==v and hit==0,(i,v,ledger.get(i))
                print(q,method,len(rr),'verified',flush=True)
        assert found==requested

if __name__=='__main__':main()
