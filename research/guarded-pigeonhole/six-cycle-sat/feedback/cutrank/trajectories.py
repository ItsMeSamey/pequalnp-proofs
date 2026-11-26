"""Time-expanded switch wiring and permutation orbits."""
def orbits(succ):
    label={}
    paths=[]
    for a in range(len(succ)):
        if a in label:continue
        paths.append([])
        while a not in label:
            label[a]=len(paths)-1
            paths[-1].append(a)
            a=succ[a]
    return label,paths


def switch(succ,ab):
    a,b=ab
    succ[a],succ[b]=succ[b],succ[a]


def fixture(n,triples,feedback):
    H=2*len(triples)+1
    succ=[(i+1)*n+j if i+1<H else feedback[j] for i in range(H) for j in range(n)]
    chords=[]
    for i,(a,b,c) in enumerate(triples):
        chords.extend([((2*i)*n+a,(2*i)*n+b),((2*i+1)*n+a,(2*i+1)*n+c)])
    return succ,chords,(H-1)*n


