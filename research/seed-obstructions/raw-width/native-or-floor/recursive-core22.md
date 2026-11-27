# At least 22 OR gates on each native bank

Deleting four private points refunds four OR gates. The remaining 16-literal core requires at least 18. A recursive certificate establishes the latter bound directly on the signed rows, using ordinary restrictions, signed deletion refunds, and first-OR exclusions. At each first-OR exclusion, the child bound for every literal rules out two OR refunds when that literal is set to zero. This limits how often any literal can appear explicitly in the first OR's arms, and the signed rows exclude every remaining choice of operands.

Extract `native-all-four-or22-recursive.zip` and run `python -B checksub.py`. The checker verifies the 1,574 subinstances and their 2,439 child references from the original rows. There are 102 first-OR exclusions, 1,459 single-child restrictions and 13 zero bounds. Each child removes exactly one active literal, so the bounds follow by induction on the number of literals. The replay uses only the Python standard library.

All four full native banks therefore require at least 22 ORs with unrestricted AND count and sharing. A separator at area 33 could use at most 11 ANDs. The certificate leaves existence at area 33 open.
