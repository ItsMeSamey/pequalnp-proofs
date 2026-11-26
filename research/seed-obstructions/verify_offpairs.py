from itertools import combinations
from verify_mixed import coords, target

for j in range(7):
    neighborhood = {(6+j+d)%13 for d in [0,1,3,9]}
    outside = sorted(set(range(13)) - neighborhood)
    negatives = [coords(k)[0] for k in range(676)
                 if not (target >> k & 1) and coords(k)[1] >> j & 1]
    for x,y in combinations(outside,2):
        pair = (1<<x) | (1<<y)
        assert any(not pair & ~mask for mask in negatives)
    print('line', 6+j, 'all 36 outside pairs dominated')
