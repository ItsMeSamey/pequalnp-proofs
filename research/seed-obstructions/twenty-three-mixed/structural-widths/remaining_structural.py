"""Necessary widths for a normalized total≤33 separator. No existential claim."""
from pathlib import Path
from collections import defaultdict
root=Path(__file__).resolve().parent
complete23={(11,7),(11,8),(12,7),(12,8),(12,9),(12,10),(12,11),(12,12),(13,7),(13,11),(13,8),(13,9),(13,10)}
lines=['mixed\tpoint_width\tline_width\tsurplus\tmax_point_cost\tmax_line_cost']
for m in range(23,34):
    d=defaultdict(list);budget=33-m
    for p in range(11,m-5):
        point_floor={11:9,12:5}.get(p,0)
        for l in range(7,8+budget-point_floor):
            k=m+1-p-l
            if k<0:continue
            if p>20 or p+l-budget>27:continue
            if p+l-budget==27 and not (p==20 and 0<=l-7<=2 and k==7-2*(l-7)):continue
            if (l==7 and k<=3) or (l==8 and k<=1) or (l==9 and k==0):continue
            if m==23 and (p,l) in complete23:continue
            d[p].append(l)
            lines.append(f'{m}\t{p}\t{l}\t{k}\t{budget-(l-7)}\t{budget-point_floor}')
    print(m,sum(map(len,d.values())), ' '.join(f'{p}:{min(ls)}-{max(ls)}' for p,ls in d.items()))
(root/'remaining-structural.tsv').write_text('\n'.join(lines)+'\n')
