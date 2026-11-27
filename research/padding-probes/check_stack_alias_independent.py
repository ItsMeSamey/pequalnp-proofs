"""Bounded 04 check of alias-frontier languages and physical outcomes."""
from collections import defaultdict
from itertools import product
from padding_cnf import encode
from stack_alias import alias_dag, decode_alias
from stack_padding import padding_dag
from stack_probe import probe


def paths(dag):
    es,s,t=dag
    out=defaultdict(list)
    for u,b,v in es:
        assert u<v
        out[u].append((b,v))
    answers=defaultdict(list)
    todo=[(s,b'',(s,))]
    while todo:
        u,word,walk=todo.pop()
        if u==t:
            answers[word].append(walk)
        else:
            for ch,v in out[u]:
                todo.append((v,word+bytes([ch]),walk+(v,)))
    return answers


def language(n,aliases,challenge):
    slots=[(abs(a),int(a<0)) if isinstance(a,int) else a for a in aliases]
    variables=sorted({i for i,_ in slots})
    expected={}
    for bits in product((0,1),repeat=len(variables)):
        val=dict(zip(variables,bits))
        key=sum((val[i]^c)<<j for j,(i,c) in enumerate(slots))
        expected[encode(challenge,n,key)]=(key,val)
    dag=alias_dag(challenge,n,aliases)
    words=paths(dag)
    assert set(words)==set(expected)
    for word,(key,val) in expected.items():
        assert decode_alias(word,aliases)==(n,challenge,key,val)
    for key in range(1<<(n+1)):
        word=encode(challenge,n,key)
        if word not in expected:
            try:
                decode_alias(word,aliases)
            except ValueError:
                continue
            raise AssertionError("inconsistent alias key accepted")
    return dag,words


def machine(n,challenge,alphabet):
    first=1+8+len(challenge)
    last=first+n
    end=last+1
    states=list(product(range(end+1),(False,True),(0,1)))
    table={}
    for line,bol,z in states:
        for byte in alphabet:
            hit=bol and line in (first,last) and byte==45
            dest=(min(end,line+(byte==10)),byte==10,z^int(hit))
            table[((line,bol,z),0,byte)]=(dest,'stay')
    return table,(0,True,0),0,{q:q[2] for q in states}


def main():
    n=4
    challenge=[(1,-2,3)]
    dag,words=language(n,[1,2,3,4,1],challenge)
    free=padding_dag(challenge,n)
    dpda=machine(n,challenge,{x for _,x,_ in free[0]}|{x for _,x,_ in dag[0]})
    def predict(raw):
        markers=raw.splitlines()[-(n+1):]
        return int(markers[0].startswith(b'-')!=markers[-1].startswith(b'-'))
    over=probe(*free,*dpda,predict=predict,promised=True)
    assert over['status']=='pair' and any(x['physical'] not in words for x in over['samples'])
    res=probe(*dag,*dpda,predict=predict,promised=True)
    assert res['status']=='constant' and res['value']==0
    neg,_=language(n,[1,2,-2,3,(1,1)],challenge)
    res=probe(*neg,*dpda,predict=predict,promised=True)
    assert res['status']=='constant' and res['value']==1
    mixed,mixwords=language(n,[1,2,-1,3,(2,1)],challenge)
    res=probe(*mixed,*dpda,predict=predict,promised=True)
    assert res['status']=='pair' and {x['prediction'] for x in res['samples']}=={0,1}
    for x in res['samples']:
        assert x['physical'] in mixwords and predict(x['physical'])==x['prediction']
    for kw in ({'fact_cap':0},{'step_cap':0}):
        assert probe(*mixed,*dpda,predict=predict,promised=True,**kw)['status']=='unknown'
    _,wide=language(5,[1,2,3,1,2,3],challenge)
    layers=defaultdict(set)
    for raw,walks in wide.items():
        cut=sum(map(len,raw.splitlines(keepends=True)[:1+8+len(challenge)+3]))
        layers[raw[:cut]].update(w[cut] for w in walks)
    sets=list(layers.values())
    assert len(sets)==8 and all(not a&b for i,a in enumerate(sets) for b in sets[:i])
    print("alias original languages/decoder exact on four fibres; independent false pair; constants 0/1; physical pair and caps; 8 disjoint cut states")


if __name__=="__main__":
    main()
