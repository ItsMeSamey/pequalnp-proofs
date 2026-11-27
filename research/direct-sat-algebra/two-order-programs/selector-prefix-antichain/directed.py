"""Certified translated containment when the allowed boundary shifts have equality blocks."""
from prefix import ROOT,binary_model
import sys
sys.path.insert(0,str(ROOT/'selector-coset-native'))
from coset import TailOrbits,from_forbidden,insert,translate

class BlockTranslation:
    directed=True
    def __init__(self,n):
        self.orbits=TailOrbits(n)
        self.tests=0
        self.strict=0
        self.declines=0
        self.layer=None

    def __call__(self,j,front,left,right,banks,selectors):
        O=self.orbits
        lk,_=O.key(j,front,left,banks,selectors)
        rk,_=O.key(j,front,right,banks,selectors)
        if lk==rk:return True
        if self.layer!=j:
            self.layer=j;self.cached={}
            self.columns=[sum(((raw>>(v-1))&1)<<h for h,raw in enumerate(O.basis)) for v in front]
            nonzero=set(self.columns)-{0}
            independent={}
            for col in nonzero:insert(independent,col,0)
            self.active=len(independent)==len(nonzero)
            self.labels={v:i+1 for i,v in enumerate(sorted(nonzero))}
        if not self.active:
            self.declines+=1
            return False
        if left not in self.cached:self.cached[left]=from_forbidden(front,left)
        if right not in self.cached:self.cached[right]=from_forbidden(front,right)
        A,B=self.cached[left],self.cached[right]
        index=dict(zip(front,self.columns))
        constraints=[]
        for scope,table in A.items():
            if not scope:continue
            for pattern in range(1<<len(scope)):
                if not translate(table,pattern)&~B[scope]:continue
                row=[];possible=True
                for i,v in enumerate(scope):
                    bit=(pattern>>i)&1
                    col=index[v]
                    if not col:
                        if bit:possible=False
                    else:row.append(-self.labels[col] if bit else self.labels[col])
                if possible:constraints.append(tuple(row))
        self.tests+=1
        result=binary_model(len(self.labels),constraints)
        if result is None:return False
        self.strict+=1
        return True
