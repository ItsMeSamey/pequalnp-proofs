# A five-port bound for 117 near-original donor banks

All 117 specified donor banks require at least 30 replacement gates when the five original output taps and all 141 retained gates remain charged. The certified lower bounds are 30 for 37 banks, 31 for 32 banks and 32 for 48 banks. A total of 170 gates allows 29 replacement gates. Other donor banks, different cuts and changes to the retained output circuit remain open.

## Reproduce

Run `python3 -I -B check.py` from this directory, using Python 3.10 or later and its standard library. The checker regenerates the bank family and all direct-cell witnesses in `certificates.json`, then checks that the reproduced records match the frozen file. Cell number `32*r+c` denotes zero-indexed row r and column c. The two triples recorded for each conflicting pair list the center, the neighbor obtained by toggling the first donor, and the neighbor obtained by toggling the second. [Derivation and scope](PROOF.md)

The 32 row masks in `statement.txt` reproduce the public L-meta-20579 mathematical statement. The source control has 180 gates and output wire 243. Appending NOT(121) supplies the retained marker at wire 244, with hexadecimal diagonal mask 35. The checker compares its control output with the posted graph on all 1,024 promised cells. The source is pinned at commit `624acb3fb2189a78719c262c1af407bd73fb3b5c`; its Apache 2.0 license is included. [Upstream control](https://github.com/open-goat/pequalnp-proofs/blob/624acb3fb2189a78719c262c1af407bd73fb3b5c/lean/PEqualNP/Outside/L_meta_20578.lean)
