# Three hidden products excluded in MaximumFive

For every `c : MaximumFive`, Lean proves `(hiddenFirst c.toFiveProgram).1.length ≠ 3`. The proof covers all 335 original keys in both modes. Its certificate uses 4,774 hints. This closes the three-hidden-product case for the normalized five-product witness. The two-hidden-product case is a separate obligation.

The source of `Research.Graph9822Planes.no_original_three` has SHA-256 `a3f0f7b9e0a5f2f39d31c2bf2227dd289c70286d1b676b79bba490c273630b6b`; its compiled object has SHA-256 `66b0a04f7ca860fa3df4cec9fb9c13a6e648e7a160ae819a3aadba6df173bf1c`. The terminal axiom report at 10:23:35 UTC lists `propext`, `Classical.choice` and `Quot.sound`.

The freeze covers 679 project modules including the terminal axiom printer and records 11 external inputs. The independently frozen checksum list has SHA-256 `1d0e89d9a727edf92d498adc6c2fd7c8809b772d6050cde6e5e62a69c8a1db17`. To verify the archived materials, extract the tarball in an empty directory and run `sha256sum -c SHA256SUMS`. Publication verified every archived checksum after extraction. The kernel result comes from the recorded Lean build.
