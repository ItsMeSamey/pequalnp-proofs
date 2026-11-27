"""Native matching certificates between ordered F3 palette frames."""
from collections import defaultdict
from itertools import permutations


def prism_certificates(edges, palettes):
    """Use validated palette maps vertex -> site, returning original edge witnesses.

    A key (i,j,e) means that orientation s_i equals e*s_j in F3. Its value
    is an ordered triple of edges, going from sites 0,1,2 of i to distinct
    sites of j. Several graph vertices may represent a single site.
    """
    membership = defaultdict(list)
    for i,pal in enumerate(palettes):
        for v,site in pal.items():
            if type(site) is not int or site not in (0,1,2):
                raise ValueError("invalid palette site")
            membership[v].append((i,site))
    observed = defaultdict(dict)
    for u,v in edges:
        if u == v:
            raise ValueError("expected loopless graph")
        for i,a in membership[u]:
            for j,b in membership[v]:
                if i < j:
                    observed[i,j].setdefault((a,b),(u,v))
                elif j < i:
                    observed[j,i].setdefault((b,a),(v,u))
    result = {}
    for (i,j), site_edges in observed.items():
        for p in permutations(range(3)):
            if all((a,p[a]) in site_edges for a in range(3)):
                slope = (p[1]-p[0]) % 3
                result.setdefault((i,j,slope), tuple(site_edges[a,p[a]] for a in range(3)))
    return result


def prism_rows(edges, palettes):
    """Return triples (i,j,e) giving homogeneous equations for frame slopes."""
    return tuple(sorted(prism_certificates(edges,palettes)))


def lift_double_prism(a, sa, b, sb, first=(0,1,2), second=(0,1,2)):
    """Choose the private middle frame for two successive three-edge matchings.

    The endpoint colours are a+sa*i and b+sb*i. The two permutations map
    left sites to middle sites and middle sites to right sites respectively.
    Return (middle translation,slope), or None if no extension exists.
    """
    if a not in (0,1,2) or b not in (0,1,2) or sa not in (1,2) or sb not in (1,2):
        raise ValueError("invalid endpoint frame")
    if sorted(first)!=[0,1,2] or sorted(second)!=[0,1,2]:
        raise ValueError("invalid site permutation")
    sm = ((first[1]-first[0])*sa) % 3
    if sm != ((second[1]-second[0])*sb) % 3:
        return None
    avoid = {(a-sm*first[0]) % 3, (b+sb*second[0]) % 3}
    return next(t for t in range(3) if t not in avoid),sm


def orientation_classes(count, rows):
    """Return (representative, scale) for each nonzero slope, or None on conflict."""
    links=[[] for _ in range(count)]
    for i,j,e in rows:
        if not 0<=i<count or not 0<=j<count or e not in (1,2):
            raise ValueError("invalid signed orientation row")
        links[i].append((j,e))
        links[j].append((i,e))
    result=[None]*count
    for root in range(count):
        if result[root] is not None:
            continue
        result[root]=(root,1)
        work=[root]
        for i in work:
            for j,e in links[i]:
                proposed=(root,result[i][1]*e%3)
                if result[j] is None:
                    result[j]=proposed
                    work.append(j)
                elif result[j]!=proposed:
                    return None
    return tuple(result)
