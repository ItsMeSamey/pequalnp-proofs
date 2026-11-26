from collections import Counter
from itertools import combinations, product
faces=[{x for x in range(16) if (x>>i&1)==a and (x>>j&1)==b}
       for i,j in combinations(range(4),2) for a,b in product(range(2),repeat=2)]
print(Counter(sum(len(face-set(holes))<=1 for face in faces)
              for holes in combinations(range(16),5)))
