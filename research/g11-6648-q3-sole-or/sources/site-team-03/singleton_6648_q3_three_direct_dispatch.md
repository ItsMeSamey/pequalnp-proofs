# M=x OR D at x=3, q=3, three direct dirty-AND-reading OR gates

All below concerns a dirty AND D. Count its secondary ancestor gates by physical index, not the number of paths or dirty pins. A plus means a raw-positive secondary receiver, a minus a raw-empty receiver.

| Secondary ancestors of D | Upstream signs | Other signs and placement | c=0 | c≥1 |
|---|---|---|---|---|
| 0 | none | ++, +−, −+, −−; before, incomparable with, or after M, in any valid order | zero-upstream proof | zero-upstream proof |
| 1 | + | + outside D, including before or incomparable with M | 08 outside-positive §Escape to T (including j=3 and 4) | 08 outside-positive |
| 1 | + | − outside D | impossible: last empty must reach a centreless top | 08 positive-upstream last-empty |
| 1 | − | + outside D | at most 6 from the two protected upstream arms; see below | empty-upstream count below |
| 1 | − | − outside D | impossible; also the same ≤6 bound | empty-upstream count below |
| 2 | ++ | both upstream, either relative order or incomparable | impossible by external D reader | two-upstream positive proof |
| 2 | +− / −+ | both upstream, either relative order or incomparable | impossible by external D reader | two-upstream mixed proof |
| 2 | −− | both upstream, either relative order or incomparable | impossible by external D reader | two-upstream empty proof |

Files in this directory: singleton_6648_q3_three_direct_zero_upstream.md (SHA e122bfb6…), singleton_6648_q3_three_direct_two_upstream.md (1d776305…), singleton_6648_protected_pair_corners.md (39604145…). The two 08 notes are /workspace/scratch/site-team-08/6648/q3-sole-or-positive-upstream-outside-positive.md (e5dd4e2e…) and q3-sole-or-positive-upstream-last-empty.md (dcf1be25…). A last empty receiver outside D cannot OR-reach M or the upstream secondary (otherwise it reaches D), and has no further direct dirty-to-OR exit available. It must reach a centreless clean terminal along ANDs. This is why its c=0 entry is impossible even if the physical gate precedes M by index.

## One empty upstream receiver

Write E=A OR B in D's ancestry, with E empty. A,B are dirty AND products on anchored pure clauses: there is no earlier exceptional ancestor of E. D expands into two original anchored products, both protected on G−9,G−10. D can have several AND-only uses of E but one global choice of its arm suffices. At most three original residuals per protected product follow from the two induced matching deletions, independently of U. Globally set D=false, M=x to allocate remaining edges.

An external AND-only path from D reaches the outside paid receiver or a centreless T_D requiring D. In the first case its dirty inlet is killed; forward the other pin even when it is raw-empty or contains E multiplicatively. Only the upstream empty selector remains, with no way to enter positive raw OR reach: E's dirty AND continuations could only have entered an OR at the now-bypassed gate or M, which forwards x. All ordinary projections therefore give only original stars, and each centreless top needs ≤2 anchored modes. At c=0 this gives U≤6≤j+3 from D alone, without a sparse threshold. At c≥1 strict failure implies U≥9, so by protected_pair_corners the count is ≤2+2c+1, sufficient.

In the other case remove T_D on D-negative inputs, so c≥1. If the outside receiver is empty, ordinary terms again give only stars and each nonomitted top takes ≤4 modes. With two protected D modes this gives B≤2+4(c−1)=4c−2 nominal modes. Including one surplus suffices at 2c≤j+4, or the target is already ≥16, with only j=3,c=4 left. Strict failure there implies s≤1. Both secondary gates empty imply unique lifted raw semantics sigma(x)=M, all others raw; no empty OR can enter the raw side of a positive gate since all paid gates are direct dirty AND readers. Then lambda=0 and t≤1 ordinary top. The gate count is below 21.

If the outside receiver is positive, there is at most one ordinary correction: its dirty supplier times its opposite raw guard. That supplier may contain upstream E, hence ≤2 clean anchored modes. With two protected D modes and four per nonomitted top, B≤4c nominal modes. Including one surplus works when 2c≤j+2 or target≥16. Remaining j=3,c=3 has B=target=12 and failure s≤3 forbids all surplus. For c=4,j=3,4 failure forces s≤1. There is only one optional positive supplier on top of the mandatory x-to-M raw substitution. The two singleton signals at a given vertex are comparable (the optional supplier can only arrive with its raw partner in that support), so no singleton lambda union survives irredundancy. At a lone raw star uv this optional supplier cannot vary both endpoints, forcing all tops to use the same fixed signal at one end; factoring gives t≤1. At no stars t=lambda=0. The resulting gate count j+3+2c−1+2t+lambda is below 21. This proves all cells, using U≤2c+j+3 to conclude the issued selected-family inequality by balance.

The sign/placement dispatch is a source proof. It does not assert a Lean certificate or completed independent review. No numerical search was run.
