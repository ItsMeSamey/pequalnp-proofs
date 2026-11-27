# Lower bounds for the fixed three-term window

The three ports replace wires 213, 222 and 225 of the supplied control. The retained terms are the other wires from 213 through 228, inclusive. The downstream result is their OR together with the OR of the replacement ports. Equivalently, one merged port can represent the contribution of all three. On each of the 1,024 promised cells, a graph zero forces the port OR to zero. A graph one with all retained terms zero forces the port OR to one. The remaining cells impose no constraint on the port OR. Use the graph in [statement.txt](statement.txt), indexed by row and then by column bit, and the bank in [witnesses.json](witnesses.json), in its listed order. The bank has 15 wires. A bank wire is available as one Boolean source, irrespective of the cost of producing it in the fixed control.

**Claim.** With this fixed bank and downstream relation, using AND, OR and NOT with at most two listed operands per gate, any three-port replacement uses at least 14 gates. Any single merged-port replacement uses at least 16 gates. Gate counts here are local to the replacement.

## Finite witnesses

Write a bank vector as a bit mask, least significant bit first. Let P be the vectors seen at forced-one cells and N those seen at forced-zero cells. The oriented section of the witness file supplies, for every bank index j, a vector n in N with bit j clear and p in P equal to n plus bit j. Thus each donor is necessary. Moreover any extension to a Boolean function of the bank must increase along at least one edge in each coordinate. A function nonincreasing in even one coordinate fails this test.

For a monotone extension, any vector above a member of P is forced to one and any vector below a member of N is forced to zero, with order given by bitwise inclusion. The triangle section records a promised cell and its original mask for each such inference. Its resulting forced corners are shown below. Each triple gives the integer masks in the order shown in the heading. The two contexts for a pair may differ.

| Pair of bank wires | OR context, values 0,1,1 at 00,10,01 | AND context, values 0,0,1 at 10,01,11 |
|---|---|---|
| 65,102 | 144,146,656 | 2,512,514 |
| 65,107 | 72,74,1096 | 2,1024,1026 |
| 102,107 | 2,514,1026 | 512,1024,1536 |

In each context the remaining coordinates are fixed. Monotonicity forces the fourth value, giving respectively the binary OR and binary AND truth tables. Call a pair with both restrictions conflicting.

## Counting occurrences

For a gate list with g charged gates and t labeled taps, trace all available observed operands backward from those taps. AND and OR observe each supplied pin up to arity two. An absent list entry is omitted from the Boolean fold (empty AND is true and empty OR is false). An explicitly listed unavailable wire, including a forward or self-reference, reads false. NOT observes only its first operand, defaulting to false if absent or unavailable, and complements it. An unavailable tap reads false. For counting, each unavailable or absent slot contributes no producer edge. A fixed-false sentinel supplies no traced donor edge. A constructed constant costs its gate. These conventions distinguish semantic evaluation from the occurrence count.

Let D count gates outside the trace, I count distinct traced donors beyond the s certified necessary ones, H sum two minus the number of available observed pin occurrences over traced gates plus the number of unavailable taps, and F sum use count minus one over traced producers. A producer is a donor or a live gate. Every traced producer has at least one use, and each necessary donor must be traced because the output depends only on traced sources. Repeated pins and repeated taps each count with multiplicity. Counting the same incidences at consumers and producers gives

    2(g−D) + t − H = (g−D) + s + I + F
    g + t − s = D + I + H + F.

Here s=15 and I=0. At zero slack the live graph is a forest of binary AND/OR trees in which each donor occurs once, including possible raw donor roots. For semantic analysis, join the t roots by a fresh binary OR tree, with no added gates when t=1. This analytical tree is outside g. In any monotone read-once formula, fixing all leaves except a pair leaves each intervening one-input context constant or identity. If the restriction depends on both variables, the operation at their lowest common ancestor therefore determines the binary function. Its label is fixed across contexts. A conflicting pair rules out such a formula.

## All one-slack cases

Exactly one unit can occur among D,H,F.

* If D=1, discarding the dead gate leaves the zero-slack forest, already excluded. A dead NOT can affect a shard signature, but cannot repair the computed graph.
* If H=1, either a tap is missing or a live gate has exactly one available observed operand. A missing tap inserts false into the final OR. A deficient AND/OR is constant or identity on the available operand, including singleton lists and explicit false reads. Pruning constants and identities yields a monotone read-once formula, possibly with fewer leaves. Necessity forces all donors to survive, and the conflicting pair again excludes it. A live nullary gate or a NOT with an unavailable first operand costs two units. A NOT with an available first operand costs one unit regardless of an ignored second pin. Its operand subtree contains a donor, since the remaining gates are full binary and the tree is finite. Every donor in this subtree has a unique path through the sole inversion, so the final function is nonincreasing in each such donor. The oriented edge for any one of them rules this out.
* If F=1, every live gate is a full binary AND/OR and exactly one producer q has two uses. Join the taps with the analytical OR tree. This preserves the fork, including a doubled tap, a tap plus an internal use, two identical gate pins or a raw donor fork. The paths may reconverge. The subgraph computing q is a read-once tree T, possibly a single donor. Unfold both uses to write the output as E(T,T), where E is a monotone formula with two distinct placeholder leaves and every donor outside T occurs once. This representation also covers branches meeting before a tap, since expanding the expression duplicates only the tree rooted at q.
  
  Two donors inside T cannot conflict. With other coordinates fixed, E(z,z) is constant or identity in z. Every restriction depending on both donors has their fixed lowest-common-ancestor operation in T. Two donors outside T cannot conflict either. Their leaves occur once in the fixed expression E, and after the other donors are fixed the two placeholders become constants. Every restriction depending on both donors has their fixed lowest-common-ancestor operation in E. Consequently each conflicting pair must cross the partition into donors inside and outside T. The three pairs in the table form a triangle. Placing wire 65 on either side places 102 and 107 together on the opposite side, contradicting the third pair.

Negative slack is impossible by the counting identity. For t=3 the zero- and one-slack counts are 12 and 13. For t=1 they are 14 and 15, and the very same forced port-OR values apply directly to the single output. Excluding both counts in each case proves the claims. The proof ranges over the specified bank and retained terms only.
