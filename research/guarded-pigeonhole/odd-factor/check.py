"""Verify the native odd-factor search construction on lifted K_{n,n}, n=1..4."""
from itertools import combinations, permutations


def bit(i):
    return 1 << i


def parity(mask):
    return mask.bit_count() % 2


class Network:
    def __init__(self,n):
        self.n = n
        # 0..3 are the auxiliary K4 vertices; vertex zero is r.
        self.port = [[4+v*n+j for j in range(n)] for v in range(2*n)]
        vertices = 4+2*n*n
        self.vertices = vertices
        self.chain = [0]+[ports[0] for ports in self.port]
        charged = set(self.chain)
        self.a = [bit(v) for v in range(vertices)]
        for prev,v in zip(self.chain,self.chain[1:]):
            self.a[v] ^= bit(prev)
        self.marker = bit(self.chain[-1])

        self.edges = list(combinations(range(4),2))
        self.path_edges = []
        self.cross = {}
        for ports in self.port:
            path = []
            for u,v in zip(ports,ports[1:]):
                path.append(len(self.edges))
                self.edges.append((u,v))
            self.path_edges.append(path)
        for i in range(n):
            for j in range(n):
                self.cross[i,j] = len(self.edges)
                self.edges.append((self.port[i][j],self.port[n+j][i]))

        self.incident = [0]*vertices
        for k,(u,v) in enumerate(self.edges):
            self.incident[u] |= bit(vertices+k)
            self.incident[v] |= bit(vertices+k)

        self.rows = [(v,self.incident[v],int(v in charged)) for v in range(vertices)]
        for v,w in zip(self.chain,self.chain[1:]):
            self.rows[v] = (v,self.incident[v]^self.incident[w],0)
        self.rows += [(vertices+k,self.a[u]^self.a[v],0) for k,(u,v) in enumerate(self.edges)]

    def failures(self,assignment):
        return {p for p,mask,offset in self.rows if assignment & bit(p)
                and parity(assignment & mask) != offset}

    def routed(self,perm):
        mask = 0
        for i,j in enumerate(perm):
            mask |= bit(self.cross[i,j])
            for k in self.path_edges[i][:j]+self.path_edges[self.n+j][:i]:
                mask |= bit(k)
        return mask << self.vertices

    def encode_colors(self,colors):
        # The H colors are zero. Each port-tree vertex gets its source color.
        desired = sum(bit(v) for j,ports in enumerate(self.port)
                      if colors & bit(j) for v in ports)
        q = desired
        prefix = 0
        for v in self.chain:
            prefix ^= int(bool(desired & bit(v)))
            q = (q & ~bit(v)) | (prefix << v)
        assert all(parity(self.a[v]&q) == bool(desired&bit(v)) for v in range(self.vertices))
        return q

    def symbolic(self):
        # Elements of a GF(2) polynomial's support are squarefree monomial masks.
        active = set()
        for pivot,mask,offset in self.rows:
            if offset:
                active.symmetric_difference_update({bit(pivot)})
            for k in range(mask.bit_length()):
                if mask & bit(k):
                    active.symmetric_difference_update({bit(pivot)|bit(k)})
        assert active == {self.marker}

    def check(self):
        self.symbolic()
        comm = faces = 0
        colors_to_q = [(a,self.encode_colors(a)) for a in range(1 << (2*self.n)) if parity(a)]
        # All four H vertex bits and all charged chain bits are one; the
        # remaining port-tree bits are zero.
        face_q = 15 | sum(bit(v) for v in self.chain)
        assert face_q & self.marker
        for perm in permutations(range(self.n)):
            z = self.routed(perm)
            for colors,q in colors_to_q:
                assert q & self.marker
                expected = {self.vertices+self.cross[i,j] for i,j in enumerate(perm)
                            if bool(colors & bit(i)) != bool(colors & bit(self.n+j))}
                assert expected and self.failures(z | q) == expected
                comm += 1
            for choice in range(1 << 6):
                hz = choice << self.vertices
                expected = {v for v in range(4) if
                            parity(hz & self.incident[v]) != (v == 0)}
                assert expected and self.failures(face_q | z | hz) == expected
                faces += 1
        return comm,faces


if __name__ == '__main__':
    for n in range(1,5):
        comm,faces = Network(n).check()
        print(f"K_{{{n},{n}}}: symbolic identity, {comm} matching/color pairs, {faces} Tseitin-face assignments passed.")
