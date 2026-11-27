"""Tiny full-cube oracle for an original DAG with a designated suffix boundary.

Truth table bit (2*a+b) selects a gate output. The boundary must separate the
primaries from the designated output. Metrics use the 0/1 Walsh transform.
"""
import json


def walsh(values):
    result=list(values)
    width=1
    while width<len(result):
        for start in range(0,len(result),2*width):
            for j in range(start,start+width):
                a,b=result[j],result[j+width]
                result[j],result[j+width]=a+b,a-b
        width*=2
    return result


def analyze(q,gates,boundary):
    r=len(boundary)
    if not 1<=q<=12 or not 1<=r<=8 or len(gates)>128:
        raise ValueError("tiny control cap")
    if len(set(boundary))!=r:raise ValueError("duplicate boundary")
    def evaluate(x,override=None):
        nodes=[x>>i&1 for i in range(q)]
        for i in range(q):
            if override and i in override:nodes[i]=override[i]
        for i,(table,a,b) in enumerate(gates,q):
            assert 0<=a<i and 0<=b<i and 0<=table<16
            nodes.append(override[i] if override and i in override else table>>(2*nodes[a]+nodes[b])&1)
        return nodes
    live={q+len(gates)-1}
    for i in range(q+len(gates)-1,q-1,-1):
        if i in live:
            live.remove(i)
            if i not in boundary:live.update(gates[i-q][1:])
    assert live<=set(boundary)
    hist=[0]*(1<<r)
    direct=0
    for x in range(1<<q):
        vals=evaluate(x)
        y=sum(vals[node]<<j for j,node in enumerate(boundary))
        hist[y]+=1
        direct+=vals[-1]
    h=[evaluate(0,{node:y>>j&1 for j,node in enumerate(boundary)})[-1] for y in range(1<<r)]
    spectrum=walsh(h)
    pencil=walsh(hist)
    joint=[a*b for a,b in zip(spectrum,pencil)]
    assert sum(joint)==direct<<r
    assert sum(x*y for x,y in zip(h,hist))==direct
    nz=lambda vector:sum(v!=0 for v in vector)
    return dict(q=q,r=r,count=direct,image=nz(hist),accepting_rows=nz(h),suffix_nonzero=nz(spectrum),
                pencil_nonzero=nz(pencil),joint_nonzero=nz(joint))


def make(r,name):
    q=2*r
    g=[]
    def gate(t,a,b):
        g.append((t,a,b))
        return q+len(g)-1
    def fold(t,inputs):
        result=inputs[0]
        for b in inputs[1:]:result=gate(t,result,b)
        return result
    if name=='affine-pencil':
        f=list(range(r))
    elif name=='zero-switch':
        # x0*x1 and x0*(1+x1) cannot both equal 1.
        f=[gate(8,0,1),gate(8,0,gate(3,1,1))]
        f.extend(gate(8,2*i,2*i+1) for i in range(2,r))
    else:
        f=[gate(8,2*i,2*i+1) for i in range(r)]
    if name=='parity':fold(6,f)
    elif name=='zero-switch':
        impossible=gate(8,f[0],f[1])
        gate(8,impossible,fold(6,f[2:]))
    elif name=='quadratic':
        fold(6,[gate(8,f[i],f[i+1]) for i in range(0,r,2)])
    else:fold(8,f)
    return q,g,f


def run():
    for name in ('AND','parity','quadratic','affine-pencil','zero-switch'):
        q,g,f=make(6,name)
        d=analyze(q,g,f)
        if name=='AND':assert (d['count'],d['joint_nonzero'])==(1,64)
        if name=='parity':assert (d['count'],d['joint_nonzero'])==((4**6-2**6)//2,2)
        if name=='quadratic':assert d['joint_nonzero']==64
        if name=='affine-pencil':assert d['joint_nonzero']==1
        if name=='zero-switch':assert d['count']==0 and d['accepting_rows']>0
        print(json.dumps(dict(name=name,gates=g,boundary=f,**d)))


if __name__=='__main__':
    run()
