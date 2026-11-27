# Exactly which column graphs guarantee a seven-vertex witness?

Use the original graph and intrinsic partition of [the row-pair problem](dominating-row-pair.md): z is a mandatory universal vertex, the two remaining pins p,q are nonadjacent with nonempty disjoint neighborhoods A,B in G−z, and A,B are completely joined. Assume A and B separately induce a clique or an independent set. Now the induced graph on the other unnamed sites D and its incidences with A,B are unrestricted.

For a fixed graph on D, the following are equivalent.

1. For every nonempty choice of the two homogeneous parts and every cross-incidence matrix, each YES instance admits a seven-site witness including the three original pins.
2. D is a disjoint union of cliques, or its complement is a disjoint union of cliques.

For these graphs recognition and search are polynomial, with no bound on the number of cliques or column incidences. Derive A,B,D from the original pins, try universality at each of the three names, verify the hypotheses, and test clique components in D and its complement. Search all a∈A,b∈B and unordered distinct i,j∈D. Check the seven sites z,p,q,a,b,i,j directly for even induced degrees. This uses O(n⁴) candidate tests of constant size after adjacency lookup. On the recognized class their exhaustion proves NO.

**Parity of small witnesses.** Fix an arbitrary large original witness. Let X_A,X_B,Y be its selected vertices in A,B,D, respectively. Both X classes have odd size. Removing z leaves an all-odd support, so |Y| is even. In the A/B rows restricted to Y, every selected row has odd weight since its pin and every selected opposite-class vertex together contribute even degree and its selected own-class neighbors also contribute even degree. Put F=D[Y], write g for its vector of degree parities, and let s_i,t_i count selected A,B neighbors of i modulo two. Then s+t=1+g. Write L=diag(g)+adj(F) over GF(2).

The parity of the number of seven-site witnesses within these selections is

    1 + sᵀ L g.

Indeed first set aside edges in F for the calculation, keeping the fixed row vectors unchanged. For a fixed selected pair of rows let I be their intersection size modulo two. At columns where exactly one row is 1, each of the two complementary column types has multiplicity 1+I modulo two. Thus the number of successful column pairs for these rows in an edgeless F has parity (1+I)²=1+I. Summing gives 1+s·t=1+s·g. Each actual edge ij of F reverses the success of a column pair exactly for those row pairs in which both rows distinguish i and j (in such a pair the successful patterns shift from opposite-exclusive to common-one/common-zero). Its parity correction is (s_i+s_j)(t_i+t_j). Using s+t=1+g and summing over edges gives s·g + Σ_{ij∈E(F)}(s_i+s_j)(g_i+g_j)=s·g+sᵀLg. This proves the formula.

On a disjoint union of cliques the parity vector is constant in each component, so Lg=0. On its complement, because |Y| is even, the degree parity is 1+g rather than g. The parity of the edges across the partition into g=0 and g=1 at any vertex remains unchanged: both parity classes have even size, by handshaking and |Y| even. Hence Lg is still zero in the complemented graph. Cluster and co-cluster graphs are hereditary, so each YES witness in either class contains an odd number of seven-site witnesses.

**Sharpness.** The forbidden induced graphs for the union of these two classes are the four-vertex path, the disjoint union of a three-vertex path and an isolate, and its complement (the paw). One direction follows by inspection. Conversely, a disconnected graph avoiding a three-vertex path plus an isolate can have no induced three-vertex path in a component and therefore consists of cliques. A connected graph of order at least two avoiding a four-vertex path has disconnected complement by Seinsche's theorem. If it also avoids the paw, apply the disconnected case to its complement. https://doi.org/10.1016/0095-8956(74)90063-X

For each forbidden induced subgraph take A and B to be singletons with their required join. Assign column types (A incidence,B incidence) as follows. All columns outside the four can have arbitrary edges in D as originally prescribed.

* For a path 0–1–2–3 use 00,10,01,00 in that order, filling every extra column by 00. All four selected columns work. The only pair of complementary column types present is 10/01, whose two vertices are adjacent; success would require a nonedge.
* For the path 0–1–2 and an isolate 3 use 11,01,00,01, filling extras by 01. All four work; the only complementary pair is 11/00 at the two nonadjacent path ends, where an edge would be required.
* For the paw complement the preceding four-vertex graph and flip the B bit on all its columns and fillers. On this even four-column selection graph complementation toggles all column degree parities and the B flip compensates, without changing selected row parities. For every complementary pair both its required edge bit and (on the four sites) its actual edge bit switch. The filler type has no complement anywhere, so arbitrary outside edges cannot make a successful pair.

Thus the full nine-site selection through these four columns is a raw witness, while no seven-site selection succeeds for any choices of the extra columns or their incident edges in the given D. Smaller witnesses would need nonempty even column support as well as one selected row of each class. This proves the universal statement for every fixed D. It concerns the completeness of this specific small-witness procedure; it gives no complexity lower bound for other D.

The bounded checker universal_pin_drift_check.py independently enumerates witness counts from raw adjacency. Its 569 legal full selections cover all four-vertex column graphs with singleton row classes and seeded larger cases; the general identity and arbitrary-exterior extensions above are mathematical conclusions.
