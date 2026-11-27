from component_grid_band import supplied
from source_grid_cnf_band import supplied as original

for special,r,expected in [('det',55,7),('free',57,21)]:
    cs=[]
    ps=[]
    for b in range(8):
        kind='tie' if b<7 else special
        cs.extend([((8*b+i+1)*(-1 if kind!='free' and (i==0 or (i==1 and kind=='det')) else 1),)
                   for i in range(8)])
        ps.append(tuple(16*b+(j^(kind=='free')) for j in range(16)))
    got=supplied(64,cs,ps,center=15,excess=0,digits=5,word_cap=4)
    assert (got['values'],got['order'],got['outside_bits'],got['components'],got['spent_words'],
            got['cache_hits'])==((expected,),r,56,8,4,6),got
    assert got['methods']==('cube',)*8
    assert supplied(64,cs,ps,center=15,excess=0,digits=5,word_cap=3)['status']=='unknown'
    print(special,r,got['values'])
cs=[(1,),(-2,)]
ps=[(1,0),(2,None),(None,3)]
opts=dict(center=1,excess=2,digits=3,word_cap=8)
want=original(2,cs,ps,**opts)
for cross in (-1,8):
    got=supplied(2,cs,ps,cube_bits=cross,**opts)
    assert got['values']==want['values'] and got['components']==2
# Two dormant rows, two outside cols: local ordinary collision branch includes a 4-node hafnian.
cs=[(1,),(2,)]
ps=[(0,2,None,None),(1,3,None,None)]
opts=dict(center=3,excess=0,digits=3,word_cap=2)
a=supplied(2,cs,ps,cube_bits=-1,**opts)
b=supplied(2,cs,ps,cube_bits=8,**opts)
assert a['methods']==('normalized_product',) and a['values']==b['values']
print('PASS raw 64-variable multi-digit public entries and excess convolution; small local branch comparison',a['values'])
