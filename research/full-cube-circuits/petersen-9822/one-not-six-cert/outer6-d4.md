# Six outer ANDs with four direct raw receivers

Use outer5.md and the catalogue in outer6-d6.md. With six paid reverse unions and six nondirect raws, every join produces one of those raws. Each is a pair union of primitive branches by incomparability. Each nonprimitive nonfull activation must appear among the raw masks. The mask Z of the inverter receiver is a primitive, a raw, or full. Full is impossible since the target rejects zero and live monotone H has H(0)=0.

Across 255 surviving profile IDs, outer6d4.cpp checks 6,747,154 direct placements with all sixteen MIS witnesses. Only 27723, 40994, and 41718 pass with 13,824, 384, and 967,680 raw extensions. No Z works. Checkpoint logs are outer6-d4-small.log and outer6-d4-step{0,1,2}.log.

For each direction let S contain the omitted raws. If S contains an edge, then K(S,0)=0 and F(S)=1, so that direction must see Z and H(S)=0. Every independent subset A of such S must have H(A)=0 and therefore a rejecting direction with Z absent. These conditions plus the MIS envelopes suffice for an arbitrary monotone H: take its true sets to be the upward closure of all independent assignments accepted by K(.,1). No positive rejected by K(.,0) contains such a seed, since it is contained in an omitted positive S. K1 accepts every edge by the Z condition, and K0 rejects every independent set by the MIS witnesses.

All masks inspected are unions of primitives and hence constant on trace atoms. The controls in outer6-interpolation-control.cpp use the actual sixteen MIS plus a seventeenth direction omitting edge mask 6. Marking only that direction Z passes with H=0. Additionally marking every direction omitting vertex 1 fails: H would accept that singleton yet reject its incident edge.
