# Fixed-rectangle certificate for L-meta-10007

The default problem fixes the first row shore to mask 55. Its maximal safe column shore is 546299908, with dimensions 5 by 10. The other sixteen row shores are arbitrary, including empty or repeated shores. Any solution with fewer than seventeen slots and this rectangle can be padded with empty shores and permuted into this order. Conversely a solution of the fixed problem is a solution of the original. A negative certificate for this case requires additional orbit or case arguments to obtain an unrestricted lower bound.

For each column j let I(j) be its six incident rows (the original one entries). Given row shores S_t, maximal safe completion includes j in precisely those rectangles whose S_t avoids I(j). Thus every outside row p must satisfy a disjunction over the slots t. The t-th alternative requires p in S_t and all six elements of I(j) outside S_t. These conditions are necessary and sufficient. In particular there is no guess of column owners or clique decomposition, and no maximality restriction on row shores.

For a partial assignment maintain required and forbidden row memberships in each slot. A cell (p,j) can use exactly the slots whose required shore avoids I(j) and whose forbidden shore excludes p. An empty candidate list contradicts every completion. A single candidate forces seven literals. Iterating these rules is sound; a branch simply fixes one remaining membership in both possible ways. For total assignments the local test is exact, hence branching on unassigned bits gives a finite decision procedure. The checker accepts an explicit rooted branch tree without trusting its producer. A null leaf must close by deterministic propagation. An internal node is [slot,row,zeroChild,oneChild]. JSON uses zero-based indices and the matrix's original row and column order. Every accepting tree covers the full assignment space for the chosen anchor and budget. No size-17 negative tree has been supplied.

Run these controls with Python 3:

    python3 anchor_cones.py control21.json --budget 21 --anchor -1
    python3 anchor_cones.py control22.json --budget 22

The first reconstructs the checked 21-set cover of L-meta-10011 by closing its original row shores. The second adds the exact fixed five-row shore to that cover. Each covers all 775 zero cells. A null tree at budget one with the default anchor is a negative unit control. Positive certificates are JSON objects with a "shores" array of unsigned 31-bit row masks. The resulting rectangles are exactly (S_t, columns(S_t)).
