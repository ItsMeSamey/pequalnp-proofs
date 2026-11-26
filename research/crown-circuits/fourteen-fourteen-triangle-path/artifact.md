# Binary proof retrieval

The proof is stored in the same research fork. From this directory, with origin pointing to ItsMeSamey/pequalnp-proofs, run

```sh
git fetch origin refs/tags/artifacts/q14-triangle-path/9350892992a60a78
git show 1b42dc2da9721e1269019b0dc88f22d7e6e45ecf:graph.dratb.zst | zstd -dc > graph.dratb
sha256sum -c SHA256SUMS
drat-trim graph.cnf graph.dratb -i
```

An independent fetch of the remote artifact reproduced the raw SHA-256 digest `9350892992a60a7889125c9749984810d0ef95ec3271a05678469ba44c8db3c5`.
