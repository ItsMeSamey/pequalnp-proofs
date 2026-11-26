from fractions import Fraction as F
q=379
n=q*q+q+1
d=136977
r=n-d
assert r*( (q+1)**2-d)>q*d
def g(h):return q*h//(q*q-h)
for w in (1,2):
 for k in range(q+2):
  P=F((w+1)*(k-19)*(k-20),380)
  assert P>=w*(k<=1)
  assert P+F((k-1 if k>=3 else 0),15)>=1+w*(k==0)
# Q_w sum = (w+1)*P/380
P=q*r+r*r-39*(q+1)*r+380*n
def works(T):
 for h in range(d+1):
  # s<=T-1 requires 380*14*t <=15*[380*(T-1-baseA)+2*P]
  baseA=2*n+2*d-1-g(h)
  tmax=min(r,15*(380*(T-1-baseA)+2*P)//(380*14))
  if tmax<0:continue
  baseB=2*n+d-1-g(h)
  # 2(s-baseB) >= n+h-3P/380-t/15.
  if 2*(T-1-baseB)*380*15 >= (n+h)*380*15-3*P*15-tmax*380:
   return False,h,tmax
 return True
for T in [545840,545924,545925,545926]:
 result = works(T)
 if result is not True:
  raise AssertionError((T, result))
 print(T, result)
