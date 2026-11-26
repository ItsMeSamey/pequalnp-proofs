# Kernel-checked crown OR lower bound

The physical fan-in-two monotone circuit theorem requires at least 3n−4 binary OR gates for the n-crown for n≥3. At n=12 this gives at least 32 ORs; a circuit of total size at most 40 consequently has at most eight AND gates. The total-size-40 existence question remains open.

The [source archive](sources.zip) contains 130 Lean modules. Their hashes and dependency order are listed in [the manifest](MANIFEST.tsv). The final module checks the general and specialized physical declarations and prints their axioms. The [OR audit](ExactFinalAudit.log) and [AND audit](ShardFinalAudit.log) report only propext, Classical.choice and Quot.sound. The [base-case audit](BaseFinalAudit.log) covers the finite certificate.

Run the following in a scratch directory using the fork's pinned Lean environment with the compiled PEqualNP modules on LEAN_PATH. Set SRC to the directory containing the extracted sources and CERT to this certificate directory.

```bash
set -eu
mkdir -p "$SRC"
unzip -oq "$CERT/sources.zip" -d "$SRC"
cd "$SRC"
export LEAN_PATH="$SRC:${LEAN_PATH:-}"
tail -n +2 "$CERT/MANIFEST.tsv" | while read -r module hash; do
  path=$(printf '%s' "$module" | tr . /)
  printf '%s  %s.lean\n' "$hash" "$path" | sha256sum -c -
  lean -DwarningAsError=true -o "$path.olean" "$path.lean"
done
```
