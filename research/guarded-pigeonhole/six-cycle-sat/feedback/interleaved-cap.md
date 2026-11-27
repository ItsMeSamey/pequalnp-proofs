# Two crossing clauses on four ordered probes

Use the two ordered probe cycles defined in ordered-probe-and.md, with cuts G,B,x1,x2,x3,x4 numbered 0 through 5. Bit j of the zero-based mask signifies that probe j+1 is bad. The desired condition is that each pair {x1,x3} and {x2,x4} contains a good probe.

Set the fixed feedback image array to (3,0,1,5,4,2). In that written composition order append optional native rotations (1 4 3), (0 4 3), (2 5 4) on the right. Thus the physical signal traverses the rightmost enabled rotation first and traverses fixed feedback last. Mark cuts 1 and 4. Direct orbit tracing gives the following complete table.

| Enabled mask | Accepted bad masks |
| --- | --- |
| 0 | 4,6,12 |
| 1 | 0,12 |
| 2 | 4,6 |
| 3 | 0,2 |
| 4 | 8,9 |
| 5 | 0,1,8,9 |
| 6 | none |
| 7 | 0,1,2,3 |

The union is exactly the nine satisfying bad masks. The interface reads literal goodness and therefore accommodates arbitrary literal signs whenever the supplying two ordered cycles realize those signs. The finite construction uses no isolated selector slots. Its interface contains four probes. Extending it across overlapping clauses of an arbitrary formula requires another construction.

The companion search_interleaved_caps.py enumerates feedback permutations, placements of the two cut marks, and sequences of optional rotations. It drops a sequence as soon as any switch setting accepts a forbidden bad mask, since every extension can disable subsequent switches. It drops a rotation that leaves the entire set of already achievable feedback permutations unchanged, which preserves all possible extensions. Exhausting maximum length two finds no gadget with these marked-cut and six-wire restrictions. Maximum length three recovers the displayed solution.
