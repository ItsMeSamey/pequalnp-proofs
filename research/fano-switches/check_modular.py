"""Independent modular counts on the actual labelled trees by tree recursion."""
def tree(k):
    a,b=0,1
    period=0
    while True:
        a,b=b,(a+b)%(2*k)
        period+=1
        if (a,b)==(0,1):
            break
    n=3*period
    parent=[None,0,1,2]
    for length in [n-2,n-1]:
        root=3
        for i in range(length):
            parent.append(root)
            root=len(parent)-1
    return parent


def count(parent,labels,k):
    tables=[[[0]*8 for _ in range(2)] for _ in labels]
    for t,c in zip(tables,labels):
        t[0][0]=1
        t[1][c]=1
    for v in range(len(parent)-1,0,-1):
        outer=tables[parent[v]]
        for selected in (0,1):
            child=[sum(tables[v][state][i] for state in range(2-selected)) for i in range(8)]
            outer[selected]=[sum(outer[selected][x]*child[x^y] for x in range(8))%k
                             for y in range(8)]
    return [sum(t[i] for t in tables[0])%k for i in range(8)]


if __name__=='__main__':
    for k in range(2,36):
        parent=tree(k)
        for yes in (False,True):
            labels=([1,4,2] if yes else [1,2,4])+[4]*(len(parent)-3)
            assert count(parent,labels,k)==[0]*8
            if yes:
                chosen={0,2,4}
                assert all(parent[i] not in chosen for i in chosen)
                assert {labels[i] for i in chosen}=={1,2,4}
            else:
                assert labels.count(1)==labels.count(2)==1 and parent[1]==0
                assert parent.count(0)==1
    print("All eight counts vanished in both trees for every modulus 2 through 35.")
