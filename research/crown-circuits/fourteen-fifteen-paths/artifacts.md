# Fetching and checking the binary proofs

In this checkout point origin to ItsMeSamey/pequalnp-proofs. From the directory containing the CNFs, run

```sh
git fetch origin refs/tags/artifacts/q15-triangle-p4/29db969f973a916a
git show 08b8c318d50d518d90d9f4fe53d18f581af5affc:proof.dratb.zst | zstd -dc > triangle-p4.dratb
git fetch origin refs/tags/artifacts/q15-p4-p4/ec6c8b169780516e
git show 8f9aef885113c622f5b4a9f1648bf1cd1537a1ed:proof.dratb.zst | zstd -dc > p4-p4.dratb
sha256sum triangle-p4.dratb p4-p4.dratb
drat-trim triangle-p4.cnf triangle-p4.dratb -i
drat-trim p4-p4.cnf p4-p4.dratb -i
```

Fresh remote downloads produced SHA-256 digests `29db969f973a916ac1daae8e05a88ea18704daca3d83a851f6ef8954e867d321` and `ec6c8b169780516eb47a63c7ccb89e4403c86e27688135410087ac82d8331970` respectively.
