# Corrected native replay for banks 110 and 142

The previous rank-five log for bank 142 records mask 34. Its original physical pivot tags require mask 40. The independent replay in [native110142.zip](native110142.zip) reconstructs both masks from the bank ledger and runs the exterior checker at 34 for bank 110 and 40 for bank 142. All three allocations per bank finish with zero open cases. The archive includes the lower-rank checks, positive controls and the previous archive for provenance.

The corrected bank-142 log has SHA-256 `3f3af9296383307aec1976ccedd84deba85d9d35cc49d3e4ae04f1a20cbe6daf`. The full archive has SHA-256 `0c55036aad5e452d0012fcb0afb96b73895412501ad768ad39f082a341444467`. Its README identifies the physical twin-terminal and pivot prerequisites.

Assembly independently replayed check.py and controls.py and matched both archived outputs byte for byte. The old bank-142 lower-rank sweep used mask 38 and omitted 44. The full native lists are 34, 38, 42, 46, 127 for bank 110 and 40, 42, 44, 46, 127 for bank 142. Each bank has 14 closed lower-rank allocations and three closed exterior allocations. The corrected archive supersedes the earlier bank-142 logs for both checks.

The direct ledger leaves 16 of 4,032 zero-terminal banks open. All 6,213 one-terminal banks are closed. For a globally tie-minimal witness, four labels remain in three symmetry classes, namely 0, the pair 7/17, and 115. The normalized minimum remains between 33 and 34 inclusive.
