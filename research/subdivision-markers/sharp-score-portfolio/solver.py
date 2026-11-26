"""Compress supplied binary scores. Every witness remains in original coordinates."""
from collections import defaultdict
from itertools import combinations


def xor(values):
    out = 0
    for value in values:
        out ^= value
    return out


def selected(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def linear(cols, coeff):
    return xor(cols[i] for i in selected(coeff))


def elimination(columns):
    pivots, null = {}, []
    for i,v in enumerate(columns):
        use = 1 << i
        while v:
            j = v.bit_length()-1
            if j not in pivots:
                pivots[j] = (v,use)
                break
            row,mask = pivots[j]
            v,use = v^row,use^mask
        if not v:
            null.append(use)
    return pivots,null


def decompose(pivots, value):
    coeff = 0
    for j,(row,mask) in sorted(pivots.items(), reverse=True):
        if value>>j & 1:
            value,coeff = value^row,coeff^mask
    return value,coeff


def exact(pivots, value):
    rest,coeff = decompose(pivots,value)
    if rest:
        raise ValueError("requested vector is outside the stated span")
    return coeff


def signature(pair, primal, dual):
    return linear(primal,pair[0]) ^ linear(dual,pair[1])


class Side:
    def __init__(self, original, forced_zero, active):
        _,null = elimination(v & forced_zero for v in original)
        self.orig = [linear(original,k) for k in null]
        self.pivots,kernel = elimination(v & active for v in self.orig)
        self.free = [linear(self.orig,k) for k in kernel]

    def lift(self, raw):
        return linear(self.orig,exact(self.pivots,raw))


class Context:
    def __init__(self, base, primal, dual, stats=None):
        self.stats=stats if stats is not None else defaultdict(int)
        for name in ("temporary_pair","kernel_word","two_word","merged_scores"):
            self.stats.setdefault(name,0)
        self.n=len(base)
        if not self.n == len(primal) == len(dual):
            raise ValueError("one pair of score labels is needed per ordinary column")
        self.all=(1<<self.n)-1
        if any(v < 0 for v in base):
            raise ValueError("binary columns must be nonnegative bit masks")
        self.primal,self.dual=primal,dual
        self.cycles=elimination(base)[1]
        rank_bits=max((x.bit_length() for x in base),default=0)
        self.cuts=[row for row,_ in elimination(
            sum(((v>>j)&1)<<i for i,v in enumerate(base)) for j in range(rank_bits))[0].values()]

    def valid(self, pair, score):
        c,d=pair
        return (min(c,d)>=0 and not ((c|d)&~self.all) and not (c&d) and not decompose(elimination(self.cycles)[0],c)[0]
                and not decompose(elimination(self.cuts)[0],d)[0]
                and signature(pair,self.primal,self.dual)==score)


class Chart:
    def __init__(self, ctx, deleted, contracted):
        self.active=ctx.all^(deleted|contracted)
        self.p=Side(ctx.cycles,deleted,self.active)
        self.d=Side(ctx.cuts,contracted,self.active)
        self.free=[(v,0) for v in self.p.free]+[(0,v) for v in self.d.free]
        self.h=elimination(signature(w,ctx.primal,ctx.dual) for w in self.free)[0]
        self.ctx=ctx
        rows={}
        for j,(v,_) in sorted(self.p.pivots.items()):
            for i,row in reversed(list(rows.items())):
                if v>>i & 1:
                    v ^= row
            rows[j]=v
        self.Y=sum(1<<j for j in rows)
        self.X=self.active^self.Y
        self.fund={}
        for j in selected(self.active):
            if j in rows:
                self.fund[j]=(rows[j],0)
            else:
                dual=(1<<j)|sum(((v>>j)&1)<<i for i,v in rows.items())
                self.fund[j]=(0,dual)

    def residue(self, score):
        return decompose(self.h,score)[0]

    def lift(self, raw, score):
        c,d=self.p.lift(raw[0]), self.d.lift(raw[1])
        delta=score^signature((c,d),self.ctx.primal,self.ctx.dual)
        coeff=exact(self.h,delta)
        for i in selected(coeff):
            a,b=self.free[i]
            c,d=c^a,d^b
        assert not c&d and signature((c,d),self.ctx.primal,self.ctx.dual)==score
        return c,d

    def alternative(self, q, r, witness):
        delta=self.residue(q^r)
        raw=tuple(x & self.active for x in witness)
        if not delta:
            self.ctx.stats["merged_scores"] += 1
            return r,self.lift(raw,r)
        indices=list(selected(self.active))
        t=max(q.bit_length(),r.bit_length(),*(v.bit_length() for v in self.ctx.primal+self.ctx.dual))
        columns=[]
        for i in indices:
            c,d=self.fund[i]
            score=signature((self.p.lift(c),self.d.lift(d)),self.ctx.primal,self.ctx.dual)
            a=self.residue(score)
            # The fundamental vector c|d is the i-th column of I+J.
            columns.append(min(a,a^delta) | ((c|d)<<t))
        pivots,null=elimination(columns)
        full=(1<<len(indices))-1
        z=next((z for z in null if z != full),None)
        if z is None:
            self.ctx.stats["two_word"] += 1
            for i,j in combinations(indices,2):
                rest,z_try=decompose(pivots,((1<<i)|(1<<j))<<t)
                if not rest:
                    z=z_try
                    break
        else:
            self.ctx.stats["kernel_word"] += 1
        if z is None:
            raise AssertionError("low weight selector not found above the two-seed bound")
        active_z=sum(1<<indices[i] for i in selected(z))
        a=(raw[0]&self.Y)|(raw[1]&self.X)
        for selector in (a^active_z,a^active_z^self.active):
            c=xor(self.fund[i][0] for i in selected(selector))
            d=xor(self.fund[i][1] for i in selected(selector))
            if not c&d:
                expanded=(self.p.lift(c),self.d.lift(d))
                new=self.residue(signature(expanded,self.ctx.primal,self.ctx.dual))
                assert new in (self.residue(q),self.residue(r))
                target=q if new==self.residue(q) else r
                return target,self.lift((c,d),target)
        raise AssertionError("both selectors conflict despite even conflict parity")


def safe_site(active, bank):
    """Return a common operation and one realizable witness per score."""
    for i in selected(active):
        for side in (0,1):
            keep={}
            for score,options in bank.items():
                match=next((p for p in options if not p[side]>>i & 1),None)
                if match is None:
                    break
                keep[score]=match
            else:
                return i,side,keep
    return None


def impose(i, side, deleted, contracted):
    if side==0:
        return deleted|(1<<i),contracted
    return deleted,contracted|(1<<i)


def two_seeds(ctx, seeds, deleted, contracted, limit):
    (q,r)=seeds
    seeds=dict(seeds)
    while True:
        active=ctx.all^(deleted|contracted)
        if active.bit_count()<=limit:
            return deleted,contracted,seeds
        move=safe_site(active,{k:[p] for k,p in seeds.items()})
        if move is None:
            chart=Chart(ctx,deleted,contracted)
            score,new=chart.alternative(q,r,seeds[q])
            seeds[score]=new
            move=safe_site(active,{k:[p] for k,p in seeds.items()})
            assert move is not None
        i,side,seeds=move
        deleted,contracted=impose(i,side,deleted,contracted)


def _compress_reduced(base, primal, dual, seeds, t, stats=None):
    """Return original-index deletion and contraction masks plus full seed witnesses."""
    ctx=Context(list(base),list(primal),list(dual),stats)
    if t<0 or any(x<0 or x>=1<<t for x in list(primal)+list(dual)+list(seeds)):
        raise ValueError("scores exceed the declared bit width")
    if not all(ctx.valid(pair,score) for score,pair in seeds.items()):
        raise ValueError("each seed must be an actual disjoint raw witness")
    if len(seeds)<=1:
        dmask=next(iter(seeds.values()),(0,0))[1]
        return dmask,ctx.all^dmask,dict(seeds)
    limit=1<<(t-1)
    bound=(len(seeds)*(len(seeds)-1)//2)*limit
    deleted=contracted=0
    bank={q:[v] for q,v in seeds.items()}
    while True:
        active=ctx.all^(deleted|contracted)
        if active.bit_count()<=bound:
            kept={q:v[0] for q,v in bank.items()}
            assert all(not(c&deleted or d&contracted) and ctx.valid((c,d),q)
                       for q,(c,d) in kept.items())
            return deleted,contracted,kept
        move=safe_site(active,bank)
        if move is not None:
            i,side,kept=move
            bank={q:[p] for q,p in kept.items()}
            deleted,contracted=impose(i,side,deleted,contracted)
            continue
        blocked=defaultdict(list)
        for i in selected(active):
            q=next(q for q,ws in bank.items() if all(c>>i&1 for c,d in ws))
            r=next(q for q,ws in bank.items() if all(d>>i&1 for c,d in ws))
            assert q!=r
            blocked[tuple(sorted((q,r)))].append(i)
        (q,r),sites=max(blocked.items(),key=lambda item:len(item[1]))
        assert len(sites)>limit
        ctx.stats["temporary_pair"] += 1
        _,_,new=two_seeds(ctx,{q:bank[q][0],r:bank[r][0]},deleted,contracted,limit)
        gained=False
        for target,pair in new.items():
            for i in sites:
                for side in (0,1):
                    if not pair[side]>>i&1 and all(w[side]>>i&1 for w in bank[target]):
                        gained=True
            if pair not in bank[target]:
                bank[target].append(pair)
        assert gained

def compress(base, primal, dual, seeds, t, stats=None, offsets=()):
    """Return original masks and original-coordinate witnesses, modulo common offsets."""
    base,primal,dual,offsets=map(list,(base,primal,dual,offsets))
    if t<0 or any(v<0 or v>=1<<t for v in primal+dual+list(seeds)+offsets):
        raise ValueError("scores exceed the declared bit width")
    if not offsets:
        return _compress_reduced(base,primal,dual,seeds,t,stats)
    H=elimination(offsets)[0]
    free=[i for i in range(t) if i not in H]
    def project(v):
        r,_=decompose(H,v)
        return sum(((r>>i)&1)<<j for j,i in enumerate(free))
    L,D=list(map(project,primal)),list(map(project,dual))
    ctx=Context(base,L,D)
    projected={}
    for score,pair in seeds.items():
        q=project(score)
        if not ctx.valid(pair,q):
            raise ValueError("seed witness does not realize its coset")
        projected[q]=pair
    deleted,contracted,kept=_compress_reduced(base,L,D,projected,len(free),stats)
    return deleted,contracted,{score:kept[project(score)] for score in seeds}
