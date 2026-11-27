"""Recognize reachable residual labels, including the rejecting residual."""
from boolean_value_automata import apply,dot,insert,profile
from two_state_other_order import solve,validate,value


def recognize(p,order,limit=2):
    validate(p,order)
    if limit<1:raise ValueError('positive label cap required')
    n=len(order)
    suffix=[None]*(n+1)
    suffix[n]=[p[3]] if p[3] else []
    for i in reversed(range(n)):
        table={};basis=[]
        for rows in p[2][i]:
            for col in suffix[i+1]:
                vec=sum(dot(row,col)<<j for j,row in enumerate(rows))
                if insert(table,vec,0):basis.append(vec)
        suffix[i]=basis
    current=[(p[1],0)];widths=[1];layers=[]
    for i,variable in enumerate(order):
        lookup={};nxt=[];layer=[]
        for bit,rows in enumerate(p[2][i]):
            dest=[]
            for state,prefix in current:
                row=apply(state,rows)
                key=profile(row,suffix[i+1])
                if key not in lookup:
                    lookup[key]=len(nxt)
                    nxt.append((row,prefix|(bit<<variable)))
                    if len(nxt)>limit:
                        return None,{'cut':i+1,'prefixes':[v for _,v in nxt],
                                     'signatures':list(lookup)}
                dest.append(1<<lookup[key])
            layer.append(tuple(dest))
        layers.append(tuple(layer));widths.append(len(nxt));current=nxt
    terminal=sum(dot(u,p[3])<<j for j,(u,_) in enumerate(current))
    return (widths,1,layers,terminal),{'max_labels':max(widths)}


def intersection(p,po,q,qo):
    receipts=[]
    for program,order,second,other in ((p,po,q,qo),(q,qo,p,po)):
        det,receipt=recognize(program,order)
        receipts.append(receipt)
        if det is None:continue
        r=solve(det,order,second,other)
        if r['status']=='sat' and not (value(p,po,r['witness']) and value(q,qo,r['witness'])):
            raise AssertionError('original joint replay failed')
        r['label_checks']=receipts
        return r
    return {'status':'skip','label_checks':receipts}
