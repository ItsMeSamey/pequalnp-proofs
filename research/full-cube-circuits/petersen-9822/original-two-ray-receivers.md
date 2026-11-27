# Two ray receivers are impossible in the original six-AND scan

Research.Graph9822Profiles.OuterLive.original_d2_excluded applies to a well-wired binary monotone circuit with ten inputs, at most 17 gates, an in-range output and exactly six AND gates. If it computes the listed edge function on all 1,024 assignments, its own gate-derived scan cannot have exactly two of its ten receivers satisfy RayValue. The theorem constructs the scan from the supplied gate list and output. It applies across all hidden-gate counts and does not require the circuit to be reduced.

The [kernel freeze](original-two-ray-receivers-kernel.tar.gz) contains the sources, dependency inventory and axiom receipts. The independent audit paired 135 project modules and 14 external inputs. Both original_wide_projection (12:34:13 UTC) and original_d2_excluded (12:34:17 UTC) use only propext, Classical.choice and Quot.sound. The internal SHA256SUMS digest is 5efb327fff16b9197fb9bcb9ad6b4862ff0c9221da1d991e6dd7b9a41bd4b231.

This excludes one receiver count. The full 18-gate lower bound remains open.
