# Size seven on the six-flag singleton/pair promise for word 270549407

The specification tests all 36 ordered pairs of six flags; repeated flags give singleton inputs. The upper seven gates ignore flag zero. The lower permits using that flag, and pins it only after proving the two gate savings for flags 2 and 5. The paper proof and direct enumeration both exclude six gates. The separate physical lower Lean certificate is tracked independently of this snapshot.

For the native replay, compile frontier/register21.cpp with a C++17 compiler, then in a writable copy of frontier run python run.py /absolute/path/to/the/executable. Compare keys.tsv and result.log with the frozen copies. The search checks all adequate supports including all six flags and the five remaining after flag 0 is omitted. The reductions directory contains the verified Lean seven-gate witness and its source data, and runs against the project’s pinned PEqualNP.Defs. No lease metadata is needed.
