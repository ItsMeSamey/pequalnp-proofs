# A kernel-checked 21-OR lower bound for the four native banks

On the original 676 indexed rows, each of the four optional-input banks needs at least 21 binary OR gates. Shared AND gates and fanout are unrestricted. The fitting condition requires 28 positive rows and rejects 624 indexed negative rows. It leaves the other 24 rows unconstrained.

The declaration `TightRow.Protected.Numeric.Increment.allFourNative21` takes both bank switches, a tape indexed by its OR count, and its signed fitting proof. Receipt 20261127T124854Z lists `propext`, `Classical.choice` and `Quot.sound`. The source and object for IncrementOriginal21 have SHA-256 digests d6ecbcc71490886732daae7773cb265d74ee366d9132bcdb0d0d2b88097ad2df and 8b51560bd15226803f620038745765041c64c476f92575d7197ebd1a2066bf2b.

The main archive and three numeric predecessors account for 91 numeric source/object pairs. The generic protected pilot and the [native deletion proof](../native-deletion-kernel-frozen.zip) supply the earlier proof stages. SHA256SUMS identifies the five archives added here. The independent provenance checker uses the original workspace paths. Its release replay checked 1,056 main-archive entries and all 91 numeric pairs. The [separate computational certificate](../protected-core23.md) gives the stronger bound of 23.
