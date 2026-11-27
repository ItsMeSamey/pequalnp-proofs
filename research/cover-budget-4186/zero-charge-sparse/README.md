# Unit 4186 supporting results

The mathematical proof excludes counterexamples to the issued statement when q=0 for arbitrary junk count. It uses global AO2 leastness and the original graph and TopForm hypotheses. Team 07 lead, r01 and r10 independently reviewed the argument. The proof is written in prose and has no Lean kernel receipt.

The Python recognizer independently classifies up to K dirty ANDs in a well-formed binary AO circuit on a given graph. If more exist, it returns the first K+1 with witnesses. A true trace retains both inputs at each AND and one at each OR. At dirty rank i there are at most i traced ANDs and i+1 raw leaves. Thus supports through K+2 suffice. Only raw pins referenced by the circuit are enumerated. The bit running time is polynomial for each fixed K under sparse encoding. The CLI uses Python's standard JSON integer parsing limits.

Run python encoding_4186_small_witness_test.py from this directory. Independent team 07 reviewer r10 compared the frozen implementation with a full-cube oracle in 67,678 cases, checked ten malformed cases and tested two sparse instances with 10,001-bit n. The recognizer does not certify circuit minimality. These results do not establish the issued refutation.
