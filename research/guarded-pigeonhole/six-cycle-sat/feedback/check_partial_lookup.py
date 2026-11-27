"""Trace four physical three-socket selector permutations joined by four swap/reflect cells."""
from itertools import product

def response(vsel,bits):
    ans=[]
    for start in range(4):
        v=start
        port=2
        while True:
            sel=vsel[v]
            out=sel if port==2 else (2 if port==sel else port)
            if out==2:
                ans.append(v)
                break
            row,col=(v,out) if v<2 else (out,v-2)
            if bits[2*row+col]:
                if v<2:v,port=2+col,row
                else:v,port=row,col
            else:port=out
    return ans

def checked():
    count=0
    for sel in product(range(2),repeat=4):
        for bits in product(range(2),repeat=4):
            ans=response(sel,bits)
            exp=list(range(4))
            for i,j in product(range(2),repeat=2):
                if sel[i]==j and sel[2+j]==i and bits[2*i+j]:
                    exp[i],exp[2+j]=exp[2+j],exp[i]
            if ans!=exp:raise AssertionError((sel,bits,ans,exp))
            for allowed in product(range(2),repeat=4):
                p=list(range(8))
                for i in range(4):p[i]=ans[i]
                for i,en in enumerate(allowed):
                    if en:p[i],p[4+i]=p[4+i],p[i]
                for i,j in product(range(2),repeat=2):
                    u=4+i;t=6+j
                    v=p[u]
                    while v!=u and v!=t:v=p[v]
                    desired=allowed[i] and allowed[j+2] and exp[i]==j+2
                    if (v==t)!=bool(desired):raise AssertionError((p,sel,bits,i,j))
                    count+=1
    print(count,'pointwise selected row/column and private factor queries')
if __name__=='__main__':checked()
