import itertools
import random

def parity(scope,rhs):
    return [[-v if b else v for v,b in zip(scope,word)] for word in itertools.product((0,1), repeat=3) if sum(word)%2!=rhs]

def cases():
    for seed in (733181,195941):
        rng=random.Random(seed)
        def emit(name,n,rows):
            perm=rng.sample(range(1,n+1),n)
            sign=rng.choices((-1,1),k=n)
            raw=[]
            for row in rows:
                vals=[perm[abs(v)-1]*sign[abs(v)-1]*(1 if v>0 else -1) for v in row]
                rng.shuffle(vals)
                raw.append(vals)
            rng.shuffle(raw)
            return (f'{name}-{seed}',n,raw)
        for k in (3,5):
            for bad in (0,1):
                rows=[[1]]+([[-k]] if bad else [])
                for j in range(k):
                    u,v,h=j+1,(j+1)%k+1,k+j+1
                    rows.extend([[-u,v,h],[-u,v,-h]])
                yield emit(f'implication-ring-{k}-{bad}',2*k,rows)
            n=k+3
            p=[rng.randrange(2) for _ in range(n)]
            for bad in (0,1):
                rows=[[i+1 if p[i] else -(i+1)] for i in (0,1)]
                for i in range(2,n):
                    rows+=parity([i-1,i,i+1],p[i-2]^p[i-1]^p[i])
                rows+=parity([1,n-1,n],p[0]^p[-2]^p[-1]^bad)
                yield emit(f'parity-recurrence-{n}-{bad}',n,rows)
        n=10
        p=[rng.randrange(2) for _ in range(n)]
        for bad in (0,1):
            rows=[[n if p[-1] else -n]]
            for i in range(n-1):
                j=(i+1)%(n-1)
                rows+=parity([i+1,j+1,n],p[i]^p[j]^p[-1]^(bad if i==0 else 0))
            yield emit(f'parity-cycle-{bad}',n,rows)
        for n in (6,9):
            rows=[]
            for _ in range(round(4.3*n)):
                rows.append([v*rng.choice((-1,1)) for v in rng.sample(range(1,n+1),3)])
            yield emit(f'random-{n}',n,rows)
            yield emit(f'mixed-{n}',n,rows+parity([1,2,3],rng.randrange(2)))
