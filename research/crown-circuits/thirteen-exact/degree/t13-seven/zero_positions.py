from few_groups import check
import sys
tags=(1,1,1,2,2,2,4,4,4)
for k in map(int,sys.argv[1:]):
    print(k,check(3,tags,150000,starcuts='full',ordinary_position=k),flush=True)
