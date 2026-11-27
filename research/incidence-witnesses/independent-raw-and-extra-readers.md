# Simultaneous raw-pair AND and disjoint raw-reader credits

Use independent-raw-and-planted-theta.md with m≤1617 selected AND pairs. Let Q be raws outside their endpoints with W chosen excess outgoing occurrences above two. Assume 2m+|Q|≤3234. For risky-neighborhood selection only, count Q as active as well. Again at most eight risky neighborhoods per shore arise and each disjoint reserve block has size at least 395.

Extend the retained H-endpoints to a maximal independent set of H exactly as before. Retain all other raws except members of Q outside K∪R, which are additionally deleted. The full theta still dominates, and every survivor still has three neighbors by the modified risky-neighborhood test. Credits on the additional deleted raws are separate from all H charges.

The probability the planting and reserve have no internal H edge exceeds .81. Prior to conditioning, the expected chosen Q credit lost to K∪R is at most (403/N+3/395)W. Conditional on the good event, some choice therefore loses less than .01247W for W>0. This yields a simultaneous surplus of at least m+ceil(.98753W).

If |Q|≤190, exclude Q when drawing each reserve block, leaving at least 205 candidates. Reject plantings where K meets Q. The probability of any failure is bounded by

    190·403/N + 1617·(.000019+2(403/N)(3/205)+(3/205)²) < .98.

Thus in this regime every selected Q occurrence and each of the m AND-pair credits can be paid on the same restriction, for a surplus of m+W.
