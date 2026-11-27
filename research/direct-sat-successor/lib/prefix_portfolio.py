"""Affine-AND DAG normalization using linear dependence of quadratic parts."""
import sys
from pathlib import Path
import time
sys.path.insert(0,str(Path(__file__).resolve().parent.parent / 'direct-sat-portfolio'))
import portfolio as api

def bits(m):
 while m:
  x=m&-m;m-=x;yield x.bit_length()-1

def normalize(n,gates,out):
 gates=api.validate(n,gates,out)
 images=[1<<i for i in range(n+1)]
 def image(m):
  value=0
  for i in bits(m):value^=images[i]
  return value
 basis={};keep=[]
 for l,r in gates:
  a,b=image(l),image(r)
  lower=a&b
  if a&1:lower^=b&~1
  if b&1:lower^=a&~1
  q=0
  for i in bits(a>>1):
   for j in bits(b>>1):
    if i!=j:
     x,y=sorted((i,j));q^=1<<(y*(y-1)//2+x)
  while q and (p:=q.bit_length()-1) in basis:
   vec,form=basis[p];q^=vec;lower^=form
  if q:
   variable=1<<(1+n+len(keep));keep.append((a,b))
   basis[q.bit_length()-1]=(q,variable^lower);images.append(variable)
  else:images.append(lower)
 new=image(out)
 if new.bit_length()<=n+1:return (),new
 return api.compact(n,keep,new)


def solve(n, gates, output, *, prefix_budget=2_000_000, **options):
    """Exact portfolio with optional polynomial-work prefix compilation."""
    started = time.perf_counter_ns()
    original = api.validate(n, gates, output)
    api.natural('prefix_budget', prefix_budget)
    m = len(original)
    width = n + m + 1
    # m times square width is a dispatch proxy, not an upper bound on bit operations.
    bound = m * width * width
    applied = m > 0 and output.bit_length() > n+1 and bound <= prefix_budget
    transformed, last = normalize(n, original, output) if applied else (original, output)
    elapsed = time.perf_counter_ns() - started
    result = api.solve(n, transformed, last, **options)
    if result['status'] == 'sat' and not api.evaluate(n, original, output, result['witness']):
        raise RuntimeError('prefix witness failed untouched original replay')
    cost = result['cost']
    cost['prefix'] = dict(raw_n=n, original_ands=m, compiled_ands=len(transformed),
                          applied=applied, budget=prefix_budget, work_proxy=bound,
                          elapsed_ns=elapsed, replayed=result['status']=='sat')
    return result
