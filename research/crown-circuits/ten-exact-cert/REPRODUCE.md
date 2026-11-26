The upper and aggregate checks run with Python 3.10 or later. C++ source requires a C++20 compiler, and the JavaScript checkers use Node.js. Keep generated files separate from the archive for hash checking.

For four ANDs, python3 mk4.py emits the projected template stream for ten23.cpp. python3 chron4.py gives the separate chronological stream. Compile ten23.cpp with optimization and pipe each stream into its executable. The recorded streams and outcomes are distributed alongside the programs.

For five ANDs compile profiles.cpp, canonicalfive.cpp and exact.cpp, then run profiles, pipe that output into canonicalfive, and finally run exact 0 4 with the canonical stream on its standard input. Compare outputs to chron.txt, canon.txt and a5.tsv respectively.

For six ANDs build profile6.cpp, canon6.cpp, sixcheck.cpp and sixexact.cpp. Run profile6 10 4, pipe into canon6, save its stream as six-canon.txt and compare it to the decompressed canon.txt.gz. For q=0 and q=1 run sixcheck 10 q q on this stream. To replay the q=0 exact pass prefix each canonical row with its zero-based ID and feed it to sixexact 4 4. For q=1 feed the six prefixed canonical rows selected by a hit in six-q1.tsv to sixexact 3 3. Run filter-ten.py with six-canon.txt in the working directory, then run node six_anchor.js six-hard-q2.txt and node six_anchor.js six-hard-q3.txt. Compare ID, observable atom count, library count, and hit status. Run node forest_profiles.js and compare its output to six-forest.json. Run node six_forest.js six-forest.json and compare to six-forest.tsv.

For seven ANDs run python3 seven_graphs.py and compare with seven-graph.log. The separate physical proof in dependencies/or-tight.md avoids that finite graph census.
