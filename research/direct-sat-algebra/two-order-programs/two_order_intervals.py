"""Deterministic common-interval transfer for two supplied binary matrix programs."""
from itertools import product
from math import prod
from boolean_value_automata import apply, dot, insert


def tree(first,second,k):
    n=len(first)
    if sorted(first)!=list(range(n)) or sorted(second)!=list(range(n)):
        raise ValueError('orders must be permutations of the same original bits')
    pos={v:i for i,v in enumerate(second)}
    intervals={}
    for length in range(1,n+1):
        for l in range(n-length+1):
            r=l+length
            locs=[pos[v] for v in first[l:r]]
            if max(locs)-min(locs)+1!=length: continue
            start=min(locs)
            if length==1:
                intervals[l,r]=(start,())
                continue
            dist={l:0};prev={}
            for a in range(l,r):
                if a not in dist or dist[a]>=k:continue
                for b in range(a+1,r+1):
                    if (a,b) in intervals and dist[a]+1<dist.get(b,k+1):
                        dist[b]=dist[a]+1
                        prev[b]=a
            if r not in prev: continue
            children=[]
            end=r
            while end!=l:
                a=prev[end]
                children.append((a,end));end=a
            intervals[l,r]=(start,tuple(reversed(children)))
    return intervals


def multiply(a,b):
    return tuple(apply(row,b) for row in a)


def tensor_key(a,wa,b,wb):
    left=sum(x<<(wa*i) for i,x in enumerate(a))
    right=sum(x<<(wb*i) for i,x in enumerate(b))
    result=0
    while left:
        bit=left&-left
        result|=right<<((bit.bit_length()-1)*wb*len(b))
        left^=bit
    return result


def solve(p,first,q,second,*,arity_cap=3,candidate_budget=100000,tensor_bit_cap=65536):
    n=len(first)
    if min(arity_cap,candidate_budget,tensor_bit_cap)<0:raise ValueError('negative cap')
    if len(p[2])!=n or len(q[2])!=n:raise ValueError('order length mismatch')
    intervals=tree(first,second,arity_cap)
    cost={'recognized_intervals':len(intervals),'candidates':0,'max_basis':0,'max_arity':0}
    if not n:
        yes=dot(p[1],p[3]) and dot(q[1],q[3])
        return dict(status='sat',witness=0,cost=cost) if yes else dict(status='unsat',cost=cost)
    if (0,n) not in intervals:return dict(status='skip',reason='arity cap',cost=cost)

    ready={}
    def run(node):
        l,r=node
        s,children=intervals[node]
        t=s+r-l
        bits=p[0][l]*p[0][r]*q[0][s]*q[0][t]
        if bits>tensor_bit_cap:raise OverflowError('tensor key cap')
        if children:
            cost['max_arity']=max(cost['max_arity'],len(children))
            tables=[ready.pop(child) for child in children]
            planned=prod(map(len,tables))
            qorder=sorted(range(len(children)),key=lambda i:intervals[children[i]][0])
            def join(rows):
                a=rows[0][0]
                b=rows[qorder[0]][1]
                for row in rows[1:]:a=multiply(a,row[0])
                for i in qorder[1:]:b=multiply(b,rows[i][1])
                return a,b,sum(row[2] for row in rows)
            choices=(join(rows) for rows in product(*tables))
        else:
            planned=2
            choices=((p[2][l][bit],q[2][s][bit],bit<<first[l]) for bit in (0,1))
        if cost['candidates']+planned>candidate_budget:raise OverflowError('candidate cap')
        cost['candidates']+=planned
        basis={};saved=[]
        for a,b,x in choices:
            key=tensor_key(a,p[0][r],b,q[0][t])
            if insert(basis,key,0):
                saved.append((a,b,x))
        cost['max_basis']=max(cost['max_basis'],len(saved))
        return saved
    try:
        order_nodes=[]
        stack=[(0,n)]
        while stack:
            node=stack.pop()
            order_nodes.append(node)
            stack.extend(intervals[node][1])
        for node in reversed(order_nodes):
            ready[node]=run(node)
        for a,b,x in ready[(0,n)]:
            if dot(apply(p[1],a),p[3]) and dot(apply(q[1],b),q[3]):
                for prog,order in ((p,first),(q,second)):
                    row=prog[1]
                    for i,v in enumerate(order):row=apply(row,prog[2][i][x>>v&1])
                    if not dot(row,prog[3]):raise AssertionError('original replay failed')
                return dict(status='sat',witness=x,cost=cost)
        return dict(status='unsat',cost=cost)
    except OverflowError as exc:return dict(status='skip',reason=str(exc),cost=cost)
