"""One exceptional activation among three conditional switches and four full roots."""
from forest3 import forests,trees
from itertools import permutations,product
from pathlib import Path
F=(1<<128)-1
halves=[sum(1<<x for x in range(128) if x>>i&1) for i in range(7)]
def templates():
    for sz in range(1,4):
        for roots in forests(7-sz):
            if len(roots)!=4:continue
            for special in trees(sz):yield roots,special
def walk(forest,us,offset):
    queue=list(zip(forest,us))
    for j,(tree,u) in enumerate(queue,offset):
        for b,subs in enumerate(tree):
            side=halves[j] if b else F^halves[j]
            queue.extend((s,u&side) for s in subs)
    return [u for _,u in queue]
def generate():
    rows=set()
    for roots,special in templates():
        before=walk(roots,[F]*4,0)
        sides=[u&side for i,u in enumerate(before) for side in [halves[i],F^halves[i]]]
        closure={0}
        for m in sides:closure|={x|m for x in closure}
        # Permutations that preserve all ordinary activations and the primitive library.
        # A subset of stabilizer generators suffices; it merely retains more representatives.
        gens=[]
        for j in range(len(before)):
            for k in range(j,len(before)):
                perm=[(x^(1<<j)) if k==j else (x^(((x>>j^x>>k)&1)*((1<<j)|(1<<k)))) for x in range(128)]
                def act(m):return sum(1<<perm[x] for x in range(128) if m>>x&1)
                pi=list(range(len(before)));pi[j],pi[k]=k,j
                if all(act(u)==before[pi[i]] for i,u in enumerate(before)):
                    gens.append([sides.index(act(m)) for m in sides])
        recipe={0:0}
        for i,m in enumerate(sides):
            for x,r in list(recipe.items()):recipe.setdefault(x|m,r|(1<<i))
        def move(x,g):
            z=0;r=recipe[x]
            for i,v in enumerate(g):
                if r>>i&1:z|=sides[v]
            return z
        seen=set()
        for u in sorted(closure-{0,F}-set(sides)):
            if u in seen:continue
            stack=[u];seen.add(u)
            while stack:
                x=stack.pop()
                for g in gens:
                    y=move(x,g)
                    if y not in seen:seen.add(y);stack.append(y)
            row=before+walk([special],[u],len(before))
            assert len(row)==7 and sum(v==F for v in row)==4
            rows.add(tuple(row))
    return sorted(rows)
if __name__=='__main__':
    rows=generate()
    Path('single-paid.tsv').write_text(''.join(' '.join(map(str,row))+'\n' for row in rows))
    print('forest pairs',len(list(templates())),'direction profiles',len(rows))
