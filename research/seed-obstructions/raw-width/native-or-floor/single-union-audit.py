from zipfile import ZipFile
from pathlib import Path
import sys,hashlib
base,fix,delta=map(ZipFile,sys.argv[1:])
rows=lambda archive,name:set(archive.read(name).splitlines())
orig=rows(base,'single7tripledep/k.keep')
cur=rows(fix,'final1-K.rows')
add=rows(delta,'s7delta/snapfull')
assert len(orig)==2218 and len(add)==58 and orig.isdisjoint(add) and orig|add==cur
inv=lambda archive,name:set(archive.read(name).splitlines()[4:])
a=inv(base,'single7triple.in');b=inv(delta,'s7delta/snapfull.in')
assert len(a)==369 and len(b)==28 and b<=a
print('all 2276 original K rows covered; all 28 supplemental signed triples already among 369')
