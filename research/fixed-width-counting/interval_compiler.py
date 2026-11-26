"""Parsimonious CNF compiler for a supplied order of signed literals."""
from itertools import product
from random import Random

class Circuit:
    def __init__(self,n):
        self.n=n
        self.true=n+1
        self.maximum=self.true
        self.clauses=[(self.true,)]
        self.gates=[]
        self.cache={}

    def gate(self,op,left,right):
        left,right=sorted((left,right))
        if left==right: return left
        if left==-right: return -self.true if op=='and' else self.true
        neutral=self.true if op=='and' else -self.true
        if -neutral in (left,right): return -neutral
        if neutral in (left,right): return right if left==neutral else left
        key=(op,left,right)
        if key in self.cache: return self.cache[key]
        z=self.maximum+1
        self.maximum=z
        self.cache[key]=z
        self.gates.append((z,op,left,right))
        if op=='and':
            self.clauses.extend(((-z,left),(-z,right),(z,-left,-right)))
        else:
            self.clauses.extend(((z,-left),(z,-right),(-z,left,right)))
        return z

    def mux(self,s,x,y):
        return self.gate('or',self.gate('and',s,x),self.gate('and',-s,y))

    def extend(self,x):
        values=[False]+list(x)+[True]
        def read(t):
            return values[abs(t)]==(t>0)
        for v,op,a,b in self.gates:
            assert v==len(values)
            values.append((read(a) and read(b)) if op=='and' else (read(a) or read(b)))
        return values

class IntervalIndex:
    def __init__(self,circuit,sequence):
        self.c=circuit
        self.sequence=list(sequence)
        self.size=1<<(max(1,len(sequence))-1).bit_length()
        leaves=self.sequence+[-self.c.true]*(self.size-len(sequence))
        self.nodes={}
        for i,lit in enumerate(leaves):
            self.nodes[i,1]=((-lit,),(-lit,),-lit)
        self.tables={}
        width=2
        while width<=self.size:
            half=width//2
            for start in range(0,self.size,width):
                lp,ls,lzero=self.nodes[start,half]
                rp,rs,rzero=self.nodes[start+half,half]
                prefix=self.join_length(lzero,rp,lp)
                suffix=self.join_length(rzero,ls,rs)
                self.nodes[start,width]=(prefix,suffix,self.c.gate('and',lzero,rzero))
                self.tables[start,width]=(self.thresholds(ls),self.thresholds(rp))
            width*=2

    def join_length(self,use_sum,other,fallback):
        # Adding the child length flips its high bit and carries that bit up.
        shifted=other[:-1]+(-other[-1],other[-1])
        short=fallback+(-self.c.true,)
        return tuple(self.c.mux(use_sum,x,y) for x,y in zip(shifted,short))

    def digit_table(self,bits):
        exact=[self.c.true]
        for bit in bits:
            exact=([self.c.gate('and',x,-bit) for x in exact]
                   +[self.c.gate('and',x,bit) for x in exact])
        ge=[-self.c.true]*(len(exact)+1)
        for i in reversed(range(len(exact))):
            ge[i]=self.c.gate('or',exact[i],ge[i+1])
        return ge

    def thresholds(self,bits):
        k=(len(bits)+1)//2
        return 1<<k,self.digit_table(bits[:k]),self.digit_table(bits[k:])

    def covers(self,table,k):
        base,low,high=table
        a,b=divmod(k,base)
        return [(high[a+1],),(high[a],low[b])]

    def zero_witnesses(self,left,right):
        if left==right: return [(-self.sequence[left],)]
        width=1<<(left^right).bit_length()
        start=(left//width)*width
        split=start+width//2
        ls,rp=self.tables[start,width]
        return [x+y for x in self.covers(ls,split-left)
                for y in self.covers(rp,right-split+1)]

def runs(clause,positions):
    ans=[]
    for i in sorted({positions[x] for x in clause}):
        if ans and ans[-1][1]==i-1:
            ans[-1]=(ans[-1][0],i)
        else:
            ans.append((i,i))
    return ans

def compile_cnf(n,clauses,order,p):
    if sorted(order)!=list(range(-n,0))+list(range(1,n+1)):
        raise ValueError('Order must contain each signed literal once.')
    circuit=Circuit(n)
    index=IntervalIndex(circuit,order)
    positions={lit:i for i,lit in enumerate(order)}
    for clause in clauses:
        literals=set(clause)
        if any(-lit in literals for lit in literals): continue
        segments=runs(clause,positions)
        if len(segments)>p: raise ValueError('Run count exceeds p.')
        options=[index.zero_witnesses(l,r) for l,r in segments]
        for choice in product(*options):
            forbidden={z for sub in choice for z in sub}
            if -circuit.true in forbidden or any(-a in forbidden for a in forbidden): continue
            forbidden.discard(circuit.true)
            circuit.clauses.append(tuple(-a for a in sorted(forbidden)))
    return circuit

def holds(clauses,values):
    return all(any(values[abs(lit)]==(lit>0) for lit in clause) for clause in clauses)

def checks():
    rng=Random(378)
    pairs=0
    for length in range(1,10):
        c=Circuit(length)
        index=IntervalIndex(c,range(1,length+1))
        for x in product((False,True),repeat=length):
            values=c.extend(x)
            for left in range(length):
                for right in range(left,length):
                    witnesses=index.zero_witnesses(left,right)
                    says_zero=any(all(values[abs(lit)]==(lit>0) for lit in w) for w in witnesses)
                    assert says_zero==(not any(x[left:right+1]))
                    pairs+=1
    instances=100
    for i in range(instances):
        n=1+i%7
        order=[s*v for v in range(1,n+1) for s in (-1,1)]
        rng.shuffle(order)
        clauses=[]
        for _ in range(rng.randrange(8)):
            lits=[]
            for _ in range(rng.randrange(1,4)):
                a=rng.randrange(len(order))
                b=rng.randrange(a,len(order))
                lits.extend(order[a:b+1])
            clauses.append(tuple(lits))
        if i%11==0: clauses.append(())
        c=compile_cnf(n,clauses,order,3)
        assert max(map(len,c.clauses))<=12
        for x in product((False,True),repeat=n):
            assert holds(clauses,[False]+list(x))==holds(c.clauses,c.extend(x))
    print(f'{pairs} exhaustive array/interval queries and {instances} signed CNF compilations passed.')

if __name__=='__main__':
    checks()
