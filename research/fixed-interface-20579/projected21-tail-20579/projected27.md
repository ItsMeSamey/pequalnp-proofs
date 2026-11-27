# At least 27 gates for the projected21 scalar care table

Consider a single-output DAG on 21 positive input wires with binary AND, binary OR and unary NOT gates. The output must agree with the pinned care table on all specified inputs. Constant propagation and pruning can only reduce the gate count. All 21 inputs are essential. On 17 of them, the care data exhibit both directions of output change when that input alone rises. The remaining four slots are 0, 1, 3 and 4.

Let B count binary gates and N count NOT gates in a pruned circuit. There are 2B+N operand edges and 20+B+N nonoutput vertices. Every nonoutput vertex has an outgoing edge, so the total excess outdegree is B−20. There are at most B−20 vertices of outdegree greater than one. Such a vertex can be a raw input.

Each binate coordinate must have paths to the output with different NOT parities. Otherwise unfolding the circuit and pushing negations to the leaves makes all occurrences have the same sign. Starting at each binate input and following its unique outgoing edge up to its first branching vertex consequently assigns that coordinate to a well-defined group. The initial segment is common to all paths from this input to the output. In particular, there is only one path from that input to its first branch.

Fix a group G and its first-branch signal z. In a fiber obtained by fixing all inputs outside G, the output is a unary function of z. Indeed, cutting z disconnects all members of G from the output. This remains true when branch signals feed other branch signals. For each j in G the sign of the unique path from j to z is fixed by its NOT parity, independently of all inputs. The signal z is therefore unate in j with a globally fixed orientation. Wire settings can suppress a change along the path, but cannot reverse its orientation.

## Any number of NOT gates

Two care edges raising coordinates j and k that both change the output in one G-fiber force a relative orientation between the paths from j and k to z. The unary decoder on this fiber must be nonconstant, hence it either preserves both orientation signs or reverses both. The exclusive-or of the observed change directions therefore equals the exclusive-or of the two globally fixed path signs. The two edges may raise the same coordinate, in which case their directions must agree.

The finite certificate records contradictory relative orientations. A witness is either two differently directed edges for the same coordinate in a fiber, or two pairs of edges for the same pair of coordinates whose required relative orientations disagree. The two pairs may belong to different fibers: each pair separately need only agree on coordinates outside G. If all bits varying within the pairs lay in G, the contradiction would follow. Their union is consequently a forbidden monochromatic set. The 70 sets in projected-orientation-witness07.json admit no coloring by four groups. Thus at least five distinct first branches are necessary and B≥25.

## A single NOT gate

If there is only one NOT gate, each binate input has an output path through it and another avoiding it. Their shared initial path through the first branch ends strictly before this NOT on the path through it. Hence every first-branch signal of a binate group is monotone on all inputs. Within a group fiber, the output is a unary function of a monotone signal, so it cannot both rise along one increasing pair and fall along another. The varying coordinates across two such pairs in the same outside-four context must receive at least two group colors. The 63 sets witnessed in projected-three-group07.json admit no five-coloring. Hence at least six distinct first branches are necessary and B≥26 for N=1.

The case N=0 cannot match the binate care data. When N=1 there are at least 26+1 gates. When N≥2 there are at least 25+2 gates. The bound concerns this scalar tail on this projected bank.

## Replay

Run either python verify_projected27.py or python -BO verify_projected27.py alongside the pinned paid26-alias-ac6.json and the two named witness files. The standard-library verifier checks the source digest, essentiality, binateness, every edge direction, and the sets of varying coordinates. It exhausts the hypergraph colorings by backtracking; the only symmetry reduction tries just one unused color at each node.
