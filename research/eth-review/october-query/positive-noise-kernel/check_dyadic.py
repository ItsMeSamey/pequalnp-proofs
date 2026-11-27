"""Tiny hand-polynomial modular oracle, including two source bits each tied twice."""
from dyadic import probe

ports = [(0,0,0,True), (0,1,1,True), (1,0,2,True), (1,1,3,True)]
kinds = {0:"or", 1:"or", 2:"copy", 3:"copy"}
# Two primary positive units and two free unaries; G(h)=24-8h².
for j in (1, 2, 8):
    for precision in (1, 4, 7, 12):
        expected = (24 - 8 * (1 << (2*j))) % (1 << precision)
        assert probe(ports, kinds, 2, j, precision) == expected
print("12 scaled dyadic residues matched")
