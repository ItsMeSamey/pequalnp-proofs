# Counting guarded solutions by intersections of clause row spaces

Every native guarded constraint fails on a single affine flat: the bit is one and every affine guard indicator is zero. Each terminal affine disjunction fails where all its indicators vanish. This description needs no acyclicity. Include these forbidden equation systems as leaves in a supplied binary tree, retaining inconsistent and empty systems if desired.

For node T, write U_T for the span of equation masks at descendant leaves, W_T for the span of all other masks, and B_T = U_T ∩ W_T. Let w be the maximum dimension of B_T. A global assignment gives a linear functional on the row-mask space by dot product. Tabulate the number F_T(s) of functionals on U_T avoiding every descendant flat and restricting to s on B_T.

At a leaf there are 2^(dim U_T − dim B_T) functionals with a fixed restriction. Subtract the number obeying the forbidden equations as well. The subtracted number is zero for inconsistency and otherwise is 2^(dim U_T − rank of the combined equations). Gaussian elimination computes both cases, including redundant and constant equations. Thus even a leaf of arbitrarily high codimension costs only 2^w polynomial work.

For children L,R put J=B_L+B_R. Then B_T is contained in J: writing v in B_T as l+r, we have l=v+r in W_T+U_R and likewise for r. Also U_L∩U_R lies in both child boundaries. The exact contraction is

    F_T(s) = sum over functionals q on J extending s
                 F_L(q restricted to B_L) F_R(q restricted to B_R).

A pair counted by a summand agrees on the child overlap and hence glues uniquely to a functional on U_T. Its restriction to J recovers q, preventing double counting. The root count is multiplied by 2^(n−dim U_root) to account for free ambient directions.

There are at most 4^w join summands per node. Counts have O(n+1) bits. Computing bases and restriction maps by elimination gives deterministic 4^w poly(input size) time and 2^O(w) poly(input size) space for an indexed-table implementation. For recovery record one positive summand per positive table entry. At each reached leaf select a single forbidden equation whose negation is consistent with its assigned boundary. Combining these chosen equations and leaf boundary equations gives a consistent global linear system by the same gluing argument. Solve it for the witness. No conditioning of the original tree on variable pins is needed.

This parameter can remain zero with arbitrarily many terminal disjunctions, dense masks, and high-codimension leaves when their normal spaces form a direct sum, for example after an invertible global change of coordinates. Finding a good tree is a separate problem. The result is an algorithm for a supplied tree and does not bound its width for unrestricted instances.

The function compute(n, flats, tree) in span.py returns the exact count. Pass recover=True for a witness or None. Run python test_span.py for 500 seeded exact-count and witness comparisons, including dependent and inconsistent systems.
