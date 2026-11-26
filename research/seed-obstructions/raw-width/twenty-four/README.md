# At most 24 live residual inputs

For the normalized live seed-deleted residual circuit in L-meta-18968, let s count the remaining binary gates and n count distinct live raw inputs. Every candidate with s ≤ 33 satisfies n ≤ s − 9 ≤ 24. Its physical excess s + 1 − n is at least ten. Seven raw line flags are compulsory, leaving at most 17 raw point primitives. The six-field census has 246 necessary triples, down from 255.

The independent assembly reviewer verified all 21 nested hashes, the full excess-nine split, and coverage for comparable and incomparable endpoints, repeated raw inputs, and up to six optional points. The assembly uses the reviewed numerical ledgers for its component exclusions. The reviewer did not rerun every component solver. To check the assembly and census, unpack the archive and run python audit.py. A constructive separator remains open.
