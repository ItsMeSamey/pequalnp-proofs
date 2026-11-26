"""Check all viable length-six direction words with each prescribed color profile."""
from collections import Counter
from itertools import permutations

PLUS=((1,0),(0,1),(-1,-1))
MINUS=tuple((-x,-y) for x,y in PLUS)
UNIT=set(PLUS+MINUS)
DISK=UNIT|{(0,0)}


def result(word):
    a=b=0
    walk=[(a,b)]
    for x,y in word:
        a+=x
        b+=y
        walk.append((a,b))
    assert walk[-1]==(0,0)
    centers=set(DISK)
    for x,y in walk:
        centers.intersection_update((x+i,y+j) for i,j in DISK)
    return len(centers)


def profile(word):
    return Counter(result(w) for w in set(permutations(word)))


if __name__=='__main__':
    mixed=profile(PLUS+MINUS)
    same=profile(PLUS+PLUS)
    four=profile((PLUS[0],MINUS[0])*2+(PLUS[1],MINUS[1]))
    six=profile((PLUS[0],MINUS[0])*3)
    assert sum(mixed.values())==720 and not mixed[0]
    print('mixed 222:',mixed,'single-shore 222:',same,'mixed 42:',four,'mixed 6:',six)
