# Bounded fanout with distinct gate inputs preserves circuit SAT

A NAND netlist with at most two pin consumers per wire can compute every unrestricted NAND circuit with linear additional size, even when the two inputs to each gate must be different wires. No constant or tied-input primitive is needed.

For a fresh pair of primary bits a,b build the following five gates.

    g = NAND(a,b)
    h = NAND(b,g)
    j = NAND(a,h)
    k = NAND(g,j)
    c = NAND(j,k)

Here h=a OR NOT b, so j=NOT a. Since j implies g, k=a and c=1 for all four choices of a,b. Every gate uses two different wires, no unordered input pair is repeated, and each wire has at most two consumers. Use a fresh copy for each constant occurrence. A same-polarity buffer from x to a fresh wire uses NAND(x,c1) followed by NAND of that output and c2. It costs twelve gates and four fresh primary bits, consuming x once.

For every original wire w let d_w count its gate-input occurrences and its output designation, if any. When d_w≥2 build a full binary tree with d_w leaves, rooted at w, with one fresh buffer per tree edge. Give each original occurrence its own leaf, including two occurrences formerly tied at one gate. When d_w=1 use w directly; a zero-load wire needs no tree. Place each producer's tree after the producer and before its consumers. Each branch wire drives two buffer inputs, every leaf serves one occurrence, and all helper wires meet the same bound. Even originally repeated operands now have distinct wire IDs. The fresh constant names and dedicated leaves ensure no unordered gate-input pair repeats, including between copies of originally identical gates.

For a single-output original circuit with s NAND gates define E as the sum of 2d_w−2 over d_w≥2. The transformed description has exactly s+12E gates and four E additional primary bits, with E≤2(2s+1). Every original input assignment extends under every choice of these fresh bits to exactly its original output value. Projection of every accepted transformed word gives an accepted original word. In particular the satisfiability verdict is preserved in both directions, and the number of accepting primary words is multiplied by 2^(4E). Copying a designated primary output, repeated consumers, unused declared inputs and s=0 are covered by the same rule. Complementing the local NAND identities by Boolean duality gives the analogous NOR construction with a constant zero and same-polarity buffers.

Consequently a polynomial deterministic SAT decision procedure on this restricted NAND class gives one on unrestricted NAND circuits by a linear gate-count reduction. The implication does not assert an unconditional time lower bound.
