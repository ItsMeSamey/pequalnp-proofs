# Fifteen binary gates for L-meta-9822

Every full-cube circuit for the ten-input edge predicate needs at least fifteen binary AND or OR gates, even when inversion is free.

First fold constants, unary aliases and dead wires of a physical circuit. Treat each NOT as a sign on a wire, including the output. This leaves a signed binary DAG with at most the original number of binary gates. Input 3 is essential, witnessed by setting input 8 to one and every input other than 3 and 8 to zero. The output is not a literal of input 3. Some surviving binary gate therefore has a signed occurrence of raw 3 as an operand. Fix raw 3 to zero. That gate's operand becomes constant, so the gate collapses to a signed alias or constant. All remaining folds and deletions preserve the resulting function and do not increase binary size.

Mask 1015 is 1023 with bit 3 cleared. The graph in the prior L-meta-9825 differs only in edges incident with vertex 3: it uses 23 in place of 38. Their zero restrictions at 3 are the identical labeled graph. The prior theorem h1015_14 has type Face true 1015 14. By the definitions of Face and Lower, a signed binary program deriving that restricted graph must use at least fourteen binary steps. The original circuit must therefore use at least fifteen. In particular total size at most seventeen permits at most two physical NOT gates; total size at most sixteen permits at most one.

This is a mathematical deduction from the prior kernel theorem. A new standalone kernel proof of the deduction is separate. No fanout-surplus recurrence or modern finite census is needed for this statement.

Prior source: open-goat/pequalnp-proofs commit b104ff3988c176aae2db960c2a71ddf975ef047c, lean/PEqualNP/Outside/L_meta_9825.lean (SHA-256 50856c1c01d9b3f0c25984f8fed3b3162eea59b2bd48c7f017fc5ae5fabc0190). Lower is at line 754, Face at line 3839, and h1015_14 at line 4640.
