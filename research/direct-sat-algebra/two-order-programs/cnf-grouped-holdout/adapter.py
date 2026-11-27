from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'guard-cap-review'/'cnf-common-tables'))
from route import solve
def grouped(n,rows):
    ans=solve(n,rows)
    return {field:getattr(ans,field) for field in ('status','route','witness','scopes','cells','source_clauses','source_literals','generated')}
