"""Replay nearest-witness choices including the paths, not only their outputs."""
from random import Random

def main():
    rng=Random(21812)
    kept=choices=loops=0
    for trial in range(15000):
        g=2+trial%4
        n=3*g
        order=rng.sample(range(n),n)
        runs=[[a] for a in order[:4]]
        for a in order[4:]:
            if rng.randrange(5)==0:runs.append([a])
            else:rng.choice(runs).append(a)
        step=[-1]*n
        for j,run in enumerate(runs):
            for a,b in zip(run,run[1:]):step[a]=b
            step[run[-1]]=n+j if j<4 else run[0]
        entries=[]
        partition=(0,0,1,1) if trial%3 else (0,0,0,1)
        for mask in range(1<<g):
            paths=[];out=[]
            for run in runs[:4]:
                x=run[0];path=[]
                while x<n:
                    path.append(x)
                    x=step[3*(x//3)+(x%3+((mask>>(x//3))&1))%3]
                paths.append(path);out.append(x-n)
            if any(partition[i]!=partition[o] for i,o in enumerate(out)):break
            entries.append((paths,out))
        if len(entries)!=1<<g:continue
        kept+=1;loops+=len(runs)>4
        for block in (0,1):
            def proj(m):return tuple(o for j,o in enumerate(entries[m][1]) if partition[j]==block)
            targets={proj(m) for m in range(1<<g)}
            for baseline,(basepaths,_) in enumerate(entries):
                for t in targets:
                    if t==proj(baseline):continue
                    candidates=[m for m in range(1<<g) if proj(m)==t]
                    dist=min((m^baseline).bit_count() for m in candidates)
                    for m in candidates:
                        diff=m^baseline
                        if diff.bit_count()!=dist:continue
                        for j,path in enumerate(entries[m][0]):
                            if partition[j]!=block:
                                if path!=basepaths[j] or any(diff>>(x//3)&1 for x in path):
                                    raise AssertionError((step,baseline,m,j))
                        choices+=1
    print(kept,'invariant patches,',loops,'with baseline internal circuits,',choices,'nearest corrections')
if __name__=='__main__':main()
