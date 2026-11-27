import os,sys
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile
with TemporaryDirectory() as d:
 with ZipFile('/workspace/scratch/syn_bounds/s33-low/s33-n23-low.zip') as a:a.extractall(d)
 os.environ['LOW_WIDTH']='23';os.chdir(Path(d)/'all23-low');sys.path.insert(0,os.getcwd())
 from pairs import bank,Rbank,qs,classify
 from route5 import check
 for i,c,O in [(567,[24,129,4160],(1,2)),(645,[48,129,4160],(2,3)),(776,[129,177,4160],(2,3)),(822,[129,4160,4184],(1,2))]:
  j=next(k for k in range(len(bank))if set(Rbank(k))==set(qs)|set(c))
  assert classify(O,j)=='binary' and check(j,O)==0
  print(i,j,O,0)
