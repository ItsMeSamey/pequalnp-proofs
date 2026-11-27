"""Check a unique all-even induced support with many branches and chords."""
from coordinate_plane_check import rank


def solutions(adj,pins):
    return [s for s in range(1<<len(adj)) if s & pins == pins and
            all(not (s >> i & 1) or (adj[i] & s).bit_count()%2 == 0 for i in range(len(adj)))]


def cycle(n):
    return [(1<<((i-1)%n))|(1<<((i+1)%n)) for i in range(n)]


def check(n):
    base=cycle(n)
    rim=(1<<n)-1
    assert solutions(base,3)==[rim]
    hub=1<<n
    adj=[hub|(rim^((1<<i)|base[i])) for i in range(n)]+[rim]
    target=hub|3
    assert solutions(adj,target)==[hub|rim]
    assert all(d.bit_count()>2 for d in adj)
    edges=sum(d.bit_count() for d in adj)//2
    cycles=edges-n
    assert cycles==n*(n-3)//2
    assert rank(adj)==(n-2 if n%3==0 else n)
    print(n,'rim; branch vertices',len(adj),'GF2 adjacency rank',rank(adj),'cycle dimension',cycles)


if __name__=='__main__':
    for n in range(6,17,2):check(n)
