# At least 20 OR gates on each native bank

Six literal deletions each remove an OR gate and leave a 14-literal core. From that core, starting with any literal, eight deletions lead to a signed six-cycle that requires five ORs. A 13-OR core would therefore lose exactly one OR upon deleting each literal.

Flattening AND-only paths shows why equality fails. If a literal appears in arms at two different ORs, setting it to zero bypasses both. If it appears on both arms at one OR, setting it to zero kills that gate and bypasses a subsequent OR on a live path. Thus each essential literal would occur in just one arm. The first OR cannot then distinguish all required incidences from the forbidden rows. The certificate checks all 91 pairs of its possible singleton operands.

The original-row replay regenerated the 19-edge core, all 14 first-deletion paths and five distinct six-cycle boundaries. Each cycle was infeasible with four ORs and feasible with five. At area 33 the new floor permits at most 13 AND gates; existence remains open on all four banks.
