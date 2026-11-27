# One inverter and at most five AND gates

For the original ten-input edge function, the Lean theorem SignedClamp.original_one_not_no_five excludes every reduced candidate with exactly one NOT gate and at most five AND gates. The physical caller derives the conditions for all 210 finite cases. Its kernel receipt at 11:06:54 UTC records only propext, Classical.choice and Quot.sound.

The theorem Sectors.remaining_exact_sixes reduces the size-17 lower-bound obligation to excluding two reduced candidates. One uses six AND gates and eleven OR gates. The other uses one NOT gate, six AND gates and ten OR gates. Both exclusions remain open. Its kernel receipt at 11:07:12 UTC records the same three axioms.

The [frozen sources and provenance](signed-five-physical-kernel.tar.gz) cover 2,059 project modules and 19 external inputs. The independent audit matched all source and object records, including the historical ScanGrammar dependency. Archive SHA-256 is 04947fad7a47c5e5f18a65a34d3d276a6bed25d569a1e6b58ee2a7ff939e1031. The internal SHA256SUMS digest is eb56515a78e299da190f7580624d635a72cee73c5a647458b122739a82ae0401.
