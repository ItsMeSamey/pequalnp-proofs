# At least 23 OR gates on the literal bank

After four private-point deletions, the literal-only core has 16 raw inputs. If a first internal OR exists, its operands may be taken from the 16 individual literals. All 120 unordered pairs must be covered. Masks 9 and 260 are bona fide first-OR choices here even though they are supplied primitives in the richer bank.

The corrected certificate covers those 120 pairs within 149 granted hypotheses, plus one baseline control. Two compiled implementations reproduced the 148 initial entries and both additional literal cases. Granting the first OR as a free input still leaves at least 18 ORs in every suffix. Adding the paid first OR and four refunded gates gives 23. The separate no-internal-OR case needs at least 23 collector ORs in the core alone.

At area 33, the literal bank could use at most 10 ANDs. The complete lower bound on each single- and paired-compound bank remains 22 ORs.
