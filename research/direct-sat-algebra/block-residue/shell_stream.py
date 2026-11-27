"""Sparse vertex-major program for signed color fibers with interleaved observations."""
from modular_support import nonzero


def _reduce(x, rows):
    for k in sorted(rows, reverse=True):
        if x >> k & 1:
            x ^= rows[k]
    return x


class Shell:
    """Color v = low bit at 2v plus twice the bit at 2v+1.

    edges=(u,v,allowed_xor_mask); bicliques=(left,right,allowed_xor_mask).
    weights[v][c] is signed; lists[v] are physical unary masks, independent
    of weights. columns[i] is the packed syndrome contribution of bit i.
    """
    def __init__(self,n,edges,bicliques,weights,lists,columns,target,observed,precision):
        if type(n)!=int or n<0 or type(precision)!=int or precision<1:
            raise ValueError("invalid dimension or precision")
        self.n,self.precision,self.mod=n,precision,1<<precision
        self.weights=tuple(tuple(row) for row in weights)
        self.lists,self.columns,self.observed=map(tuple,(lists,columns,observed))
        if (len(self.weights)!=n or any(len(r)!=4 or any(type(w)!=int for w in r) for r in self.weights)
                or len(self.lists)!=n or len(self.columns)!=2*n or len(self.observed)!=2*n
                or any(b not in (0,1) for b in self.observed)
                or any(type(x)!=int or x<0 for x in (*self.columns,target))):
            raise ValueError("invalid unary data, syndrome, or observations")
        def mask(x):
            if type(x)!=int or not 0<=x<16:raise ValueError("invalid color mask")
            return x
        def vertex(v):
            if type(v)!=int or not 0<=v<n:raise ValueError("invalid vertex")
            return v
        for x in self.lists:mask(x)
        self.target=target
        self.edges=[]
        forward=[[] for _ in range(n)]
        for u,v,m in edges:
            u,v=sorted((vertex(u),vertex(v)))
            self.edges.append((u,v,mask(m)))
            forward[u].append((v,m))
        self.blocks=[]
        incidence=[[] for _ in range(n)]
        expiry=[[] for _ in range(n)]
        for left,right,m in bicliques:
            A=tuple(sorted(set(vertex(v) for v in left)))
            B=tuple(sorted(set(vertex(v) for v in right)))
            mask(m)
            if set(A)&set(B):raise ValueError("overlapping sides within a biclique")
            if not A or not B:continue
            k=len(self.blocks)
            self.blocks.append((A,B,m))
            for side,part,opposite in ((0,A,B),(1,B,A)):
                for v in part:incidence[v].append((2*k+side,max(opposite),m))
                expiry[max(opposite)].append(2*k+side)
        suffix=[{} for _ in range(2*n+1)]
        for i in reversed(range(2*n)):
            suffix[i]=suffix[i+1].copy()
            x=_reduce(self.columns[i],suffix[i])
            if x:suffix[i][x.bit_length()-1]=x
        start=(0,-1,(0,)*4,(0,)*(2*len(self.blocks)))
        states=[start]
        self.widths=[1]
        self.transitions=[]
        for i,col in enumerate(self.columns):
            v=i//2
            following={}
            transitions=[]
            for src,(syn,low,bans,palettes) in enumerate(states):
                for bit in (0,1):
                    new_syn=syn^(col if bit else 0)
                    if _reduce(target^new_syn,suffix[i+1]):continue
                    weight=1
                    if i%2==0:
                        key=(new_syn,bit,bans,palettes)
                    else:
                        c=low|(bit<<1)
                        if not self.lists[v]>>c&1 or bans[c]>>v&1:continue
                        if any(any(palettes[slot^1]>>b&1 and not m>>(b^c)&1
                                   for b in range(4)) for slot,last,m in incidence[v]):continue
                        if any(y==v and not m&1 for y,m in forward[v]):continue
                        future=[ban&~(1<<v) for ban in bans]
                        for y,m in forward[v]:
                            if y>v:
                                for b in range(4):
                                    if not m>>(c^b)&1:future[b]|=1<<y
                        used=list(palettes)
                        for slot,last,m in incidence[v]:
                            if v<last:used[slot]|=1<<c
                        for slot in expiry[v]:used[slot]=0
                        key=(new_syn,-1,tuple(future),tuple(used))
                        weight=self.weights[v][c]%self.mod
                    dst=following.setdefault(key,len(following))
                    transitions.append((src,dst,bit,weight))
            self.transitions.append(tuple(transitions))
            states=list(following)
            self.widths.append(len(states))
        self.end=tuple(int(syn==target) for syn,_,_,_ in states)

    def fiber(self,word):
        """Return (residue, physical color tuple or None), also at zero residue."""
        word=tuple(word)
        if len(word)!=sum(self.observed) or any(b not in (0,1) for b in word):
            raise ValueError("incorrect observed word")
        pos=0
        vals={0:1}
        parents=[]
        for flag,edges in zip(self.observed,self.transitions):
            nxt={}
            back={}
            for a,b,bit,w in edges:
                if a not in vals or (flag and bit!=word[pos]):continue
                nxt[b]=(nxt.get(b,0)+vals[a]*w)%self.mod
                back.setdefault(b,(a,bit))
            vals=nxt
            parents.append(back)
            pos+=bool(flag)
        residue=sum(v*self.end[i] for i,v in vals.items())%self.mod
        last=next((i for i in vals if self.end[i]),None)
        if last is None:return residue,None
        bits=[]
        for back in reversed(parents):
            last,bit=back[last]
            bits.append(bit)
        bits.reverse()
        colors=tuple(bits[i]+2*bits[i+1] for i in range(0,len(bits),2))
        if not self.accepts(colors) or tuple(b for b,f in zip(bits,self.observed) if f)!=word:
            raise ArithmeticError("physical replay failed")
        return residue,colors

    def accepts(self,colors):
        if len(colors)!=self.n or any(type(c)!=int or not 0<=c<4 for c in colors):return False
        if any(not self.lists[i]>>c&1 for i,c in enumerate(colors)):return False
        syn=0
        for i,col in enumerate(self.columns):
            if colors[i//2]>>(i%2)&1:syn^=col
        return (syn==self.target and all(m>>(colors[u]^colors[v])&1 for u,v,m in self.edges)
                and all(m>>(colors[u]^colors[v])&1 for A,B,m in self.blocks for u in A for v in B))

    def nonzero_fiber(self):
        """Compose with explicit modular_support. Densification costs are charged."""
        if 0 in self.widths:return None
        choices=[]
        for i,edges in enumerate(self.transitions):
            mats=[[[0]*self.widths[i+1] for _ in range(self.widths[i])] for _ in range(2)]
            for a,b,bit,w in edges:
                row=mats[bit if self.observed[i] else 0][a]
                row[b]=(row[b]+w)%self.mod
            choices.append(mats)
        padded=nonzero((1,),choices,self.end,self.precision)
        if padded is None:return None
        word=tuple(v for v,flag in zip(padded,self.observed) if flag)
        residue,colors=self.fiber(word)
        if residue==0 or colors is None:raise ArithmeticError("module witness failed replay")
        return word,residue,colors
