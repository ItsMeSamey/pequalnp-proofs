# Ten-vertex component partition crosswalk

The regular globally size-minimal receiver host has 14 edges, minimum degree one, maximum degree four, and a budget of eight decoder ORs. The receiver layer bound gives a connected component of order n and maximum degree d at least n+d−5 local ORs when d≥2. Thus a connected ten-vertex host is subcubic.

A two-vertex component contains two mixed flags. Each has its own dedicated OR injection. A connected three-vertex component has at most one pure flag, since any pure flag there is a doubleton and adjacent pure doubletons are excluded. Contract the mixed injectors first to their nonraw operands. A path from a remaining pure flag persists under these nonraw aliases unless an additional dead or redundant gate already pays its credit. Fixing the pure flag then saves another OR. An all-AND path to the output would force the output false on positive opposite-side assignments. This accounts for the full order of either small component.

In 2+8 a subcubic eight-vertex side gives at most 1+12=13 edges. Its necessary quartic gives seven local ORs in addition to the two mixed injections. In 3+7 the subcubic capacity is 3+10=13, so six local ORs are needed in addition to three small-side ORs.

The only partitions into at least three components with edge capacity fourteen are 2+2+6 and 2+3+5. The partitions 2+4+4, 3+3+4, 2+2+2+4, 2+2+3+3 and 2+2+2+2+2 have capacities 13,12,9,8,5. In 2+2+6 the six-vertex side must be quartic, needing five ORs while both K2 components pay four separate injectors. In 2+3+5 all edges must occur in K2, K3 and K5. The two K2 mixed injectors plus ordinary peeling of the K3 (at least two further ORs) leave only four, below the archived five-OR floor for K5. The K2 aliases preserve the K3 edge tests.

Thus the only other cases are connected, 4+6 and 5+5, as handled in the assembly. The degree and peeling bounds are in geometry/fourteen34/receiver-layers.md. The mixed-injection counting argument also appears in paragraph two of degree/t14-34/eleven-small-components.md with the same physical assumptions.
