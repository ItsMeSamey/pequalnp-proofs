# Retrieving the binary certificate

The proof is stored in the same research fork at tag `artifacts/q14-square-path/da910033005e209d`, commit `7dc697337e003b87dfc3074c403d8825db7511e6`. From a checkout with origin pointing to ItsMeSamey/pequalnp-proofs, fetch the tag and stream-decompress the proof. Run the final two commands from this directory.

```sh
git fetch origin refs/tags/artifacts/q14-square-path/da910033005e209d
git show 7dc697337e003b87dfc3074c403d8825db7511e6:cert-8-135282733.dratb.zst | zstd -dc > cert-8-135282733.dratb
sha256sum -c SHA256SUMS
drat-trim cert-8-135282733.cnf cert-8-135282733.dratb -i
```

A fresh fetch reproduced the raw digest `da910033005e209d805311c0d5741a5a10d0d493b90b780c8cd84fc3fe5e6781`.
