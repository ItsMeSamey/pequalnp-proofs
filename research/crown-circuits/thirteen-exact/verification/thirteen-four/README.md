# Four pure groups at size 31 with seven AND gates

The input rows reproduce quartet_models.cpp at seven ANDs and four pure groups. The six columns are the pure count, graph mask, clean-private mask, branching mask, quartet mask and dirty-private mask. Exactly 62 of the 351 records have two clean private groups. Each fails a finite test. From this directory use Python 3 to replay.

    python clean2.py > replay.log
    cmp clean2.log replay.log

Keep every pure-to-pure raw and a subset of the others. Their singletons must reject, and every pair of distinct labels must accept. Each pure pin sees the union of its incident labels. Two clean private pins U,V are used just once, each in its own terminal product. There are at least two labels outside U,V (together they touch at most eight), so one other terminal is necessary. Reserving the two collector OR gates gives output F OR (U AND P) OR (V AND Q). These two gates exhaust the total ordinary OR allowance of p−2. Each mixed raw incidence contributes at most one marked raw injection. The two branching groups are free signals. Allow every remaining computation to be any conjunction of the exposed signals, including constants. The operands F,P,Q may likewise be arbitrary products of this bank.

The checker enumerates every chronological order of the selected injections. An injection adds the disjunction of its named raw and any available conjunction. The bank is closed under intersection at each step. The checker rejects only if every ordering and product choice fails on a singleton or a pair. Each X row includes an independently reproducible restricted input after the vertical bar; the last two pure coordinates are the private groups.

The second checker clean.py also handles a single clean private group U. Reserve one collector OR and allow one ordinary OR anywhere in the chronological sequence of raw injections. Its output has form F OR (U AND P). The input bank has three other unrestricted pure group signals. This handles other private groups conservatively by giving their values directly. The completed clean.log records all 189 rows with at least one clean private group; 51 of the 127 one-clean rows and all 62 two-clean rows are refuted. Rows marked O admit no contradiction among the attempted restrictions and remain unresolved by this check.

For an independently generated CNF, replay_clean.py validates each recorded multiset of test labels against the physical incidences in its census row, chooses the shortest available refuting test, and encodes products and raw injections afresh without a label permutation symmetry. It uses PySAT with CaDiCaL and drat-trim. The proof files are intentionally generated in the caller's temporary working directory; copy rows and the chosen witness log there first.

The wider one-clean log onesat.log supplements the finite enumeration with up to four marked raw occurrences per restriction. Its union with clean.log rejects 116 one-clean and 62 two-clean records. For an independent full replay, place the sources, rows, clean.log and onesat.log in a temporary directory with python-sat and drat-trim on PATH, then run:

    python replay_clean.py clean.log onesat.log > validated.log

Each certificate is regenerated without symmetry-breaking clauses. Set DRAT_TRIM to the verifier path if it is outside PATH. The separate clique-cut.md excludes one zero-clean record via a seven-input threshold minor. The parent census hypotheses remain external to these finite calculations.

The 351-row inventory can be regenerated from the archived quartet_models.cpp. Compile it under the workspace's shared native-compiler lock, then call the resulting executable with arguments 7 4 and redirect its standard error to a temporary row file. The existing rows have SHA-256 5a79936c25b63be12555aba876c10aa894ec2d917bbf58673f33f2507e9ecb82.

The checked DRAT payload is drat-certificates.tar.gz. Its 70 formula/proof pairs cover the 178 mappings in restricted-drat.jsonl. Each JSON record contains the original physical layout, ordered abstract test-label masks, a permutation listing old coordinates in new order, and the archived certificate stem. The archive has SHA-256 f63f5c5b86d491d5d238b723c6dfc859426dfe9ba18c54cd5823b112e2af828d.
