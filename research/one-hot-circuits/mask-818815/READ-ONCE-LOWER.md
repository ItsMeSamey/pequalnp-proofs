# Independent lower-bound check for mask 818815

Reading the bits in order 6u+v gives the four rows 111111, 100111, 111000, 110000. Their set intersection consists only of column 0, and no row has that profile. The column intersection consists only of row 0, and no column has that profile. An unread row input would induce a profile contained in all the others by monotonicity. The same holds for columns. Thus all ten inputs must occur in the output cone.

For a live acyclic fan-in-at-most-two circuit with ten source inputs and g gates, the undirected graph of the cone is connected. It therefore has at least 10+g−1 distinct edges and at most 2g input pins. With g≤9, equality forces g=9, exactly two distinct parents per gate, no noninput extra source, and a tree. Each node except the output feeds exactly one gate. Thus the output has a monotone read-once formula on the ten distinct raw inputs.

Set all raw bits outside r2,r3,c1,c2 to zero and simplify the resulting tree. Each remaining singleton is rejected: r2 and r3 each miss column 3, while c1 and c2 each miss row 1. The zero input is rejected by monotonicity. The pairs r3c1, r2c1 and r2c2 are accepted; r3c2 is rejected. Each of the four variables remains essential by comparison of its positive pair against the other endpoint alone.

For an OR root, both children reject every singleton. Each of the three positive pairs must be internal to one child, so connectivity forces all four variables into one child. Both children of the simplified binary formula contain variables, a contradiction. For an AND root, each positive edge must span the root partition because the zero child rejects. The positive path forces r2,r3 into one child and c1,c2 into the other. The accepted r3c1 and r2c2 imply respectively that r3 and c2 make their own child true. Then r3c2 would be accepted as well. This uses no assumptions on same-shore pairs.

This proves the nine-gate monotone upper-bound claim false. It does not furnish a nine-gate witness.
