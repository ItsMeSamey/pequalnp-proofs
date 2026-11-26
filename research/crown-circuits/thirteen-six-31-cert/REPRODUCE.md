# Replay

Use Python 3.10 or later, Node.js with BigInt support and a C++20 compiler. No network access or third-party solver library is needed by the proof replay. The bundled ten-canon.txt.gz is the six-selector activation census from the preceding ten- and eleven-input certificates. Its signed canonization and completeness are dependencies of this reduction.

Run `python3 replay.py --census-only` to regenerate the thirteen-label projections, the sparse and hot-activation screens, the helper strata, and the positive control. Run `python3 replay.py --ordinary --profiles 41718` to check all three ordinary maximum-width strata. A profile-specific execution such as `python3 replay.py --profiles 1037 975` uses the bundled compressed hard-profile fixture and solves only the named profiles. The full census replay recomputes the fixture byte for byte. With no options the program checks every ledger row.

The methods in the ledger are direct signed enumeration, signed enumeration with mandatory port groups, and either enumerator conditioned on protected continuation bases. Each ledger row records the number of visited libraries and the hit flag. For the single fully ordinary row, the visits field counts the total systems in the three ordinary width logs.

The 23-helper positive control deliberately lies outside the lower-bound budget. Its six actual signed axes carry thirteen disjoint singleton deficits and its supplied helper mask family passes exact chronology. It tests both nonempty receiver selection and the three-private-deficit port condition.
