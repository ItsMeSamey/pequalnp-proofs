"""Compare chord cut rank and a count on cyclic word adjacencies."""
import random


def rank(rows):
    pivots = {}
    for word in rows:
        while word:
            pivot = word.bit_length()
            if pivot not in pivots:
                pivots[pivot] = word
                break
            word ^= pivots[pivot]
    return len(pivots)


def audit(word):
    n = len(word)//2
    hits = [[i for i,v in enumerate(word) if v == j] for j in range(n)]
    matrix = []
    for a,b in hits:
        matrix.append(sum(1<<j for j,(c,d) in enumerate(hits) if (a<c<b) != (a<d<b)))
    edges = list(zip(word, word[1:]+word[:1]))
    for cut in range(1<<n):
        def side(i):
            return (cut>>i)&1
        component = list(range(n))
        def find(i):
            while i != component[i]:
                i = component[i]
            return i
        for a,b in edges:
            if side(a)==side(b):
                component[find(a)] = find(b)
        ids = [find(i) for i in range(n)]
        q = [0]*n
        delta = 0
        for a,b in edges:
            if side(a)!=side(b):
                delta += 1
                if not side(a):
                    a,b = b,a
                q[ids[a]] ^= 1<<ids[b]
        predicted = delta//2-len(set(ids))+1+rank(q)
        actual = rank(matrix[i]&~cut for i in range(n) if side(i))
        if actual!=predicted:
            raise ValueError((word,cut,predicted,actual))
    return 1<<n


if __name__=="__main__":
    rng=random.Random(113789)
    comparisons=0
    for k in range(450):
        n=1+k%9
        word=list(range(n))*2
        rng.shuffle(word)
        comparisons += audit(word)
    print(f"450 Euler words, {comparisons} cuts, all ranks equal")
