"""Exact lower bounds for all 17-box one-anchor branches via rounded-down costs."""
from fractions import Fraction as Q
from itertools import chain,repeat

scale=10**8
def trace_floor(m,e):
    if not m and not e:return 0
    x=m+e
    return scale*x*x//(125*(m+2*e+e*e)-4*x*x)
def first_possible(ms,k,limit=125):
    costs=[0]+[10**30]*limit
    for m in ms:
        row=[trace_floor(m,e) for e in range(limit+1)]
        costs=[min(costs[t-e]+row[e] for e in range(t+1)) for t in range(limit+1)]
    return next((e for e,c in enumerate(costs) if c<=k*scale),None)
for a,b in [(4,13),(5,11),(6,9),(6,10),(7,8)]:
    ls=[]
    for x,y in [(a,b),(b,a)]:
        ls.append(first_possible([25-y]*x+[25]*(31-x),16))
    print(a,b,*ls,'total area at least',775+max(ls))
