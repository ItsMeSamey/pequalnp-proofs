# Exact mixed-gate complexity of the residual

Treat every monotone function of the 13 point bits and every monotone function of the seven remaining line bits as free inputs. The minimum number of additional binary monotone gates that separates the residual positives from the sampled negatives is **13**. This is also the exact minimum number of mixed gates in an ordinary residual circuit when a gate with ancestors from both sides is counted as mixed.

The certificate supplies seven ordered positive/negative pairs for each side, indexed in the 676 columns of the published theorem. For a point pair, its positive line vector is contained in its negative line vector. Thus only a point-side signal can be 1 at the positive and 0 at the negative. Furthermore, for every two point pairs, the positive point vector of one is contained in the negative point vector of the other. No monotone point function can distinguish both. The same two checks hold after interchanging points and lines for the seven line pairs.

Any monotone separator must use at least one distinguishing boundary signal per pair. The 14 pairs require 14 distinct signals. The connected output cone with those signals as leaves therefore contains at least 13 binary gates. Treating the outputs of all point-only and line-only gates as freely available sources proves the claim for arbitrary interleaved circuits with sharing. For equality use each of the seven line bits AND its four-point incidence OR, followed by six OR gates. The verifier checks that construction on all 676 columns, including the erased ones.

Run `python verify_mixed.py` from this directory. The raw decoder uses the original formal statement and the Python standard library. The full 34-gate existence question remains open.

## Equality forces all fourteen singleton signatures

A circuit with exactly 13 mixed gates must use exactly 14 boundary signals, seven for each side. They are uniquely identifiable by which of the seven disjoint pair requirements on that side they meet. For a side signal, define its signature to be the subset of coordinates on whose singleton input it is true. On a residual positive each side receives a singleton, so acceptance on that side means the corresponding coordinate belongs to its signature. If a signal rejects a negative side vector, then its signature is disjoint from that vector by monotonicity.

Take any positive/negative pair whose positive is dominated by its negative on the opposite side. At least one of the seven signatures must contain the positive coordinate and avoid every coordinate of the negative. Initialize required and forbidden membership bits from the indexed packing pairs. Whenever a constraint has only one eligible signature, add its required and forbidden bits to that signature. Iterating these forced deductions fixes every one of the 91 point-side membership bits and 49 line-side bits. The point signatures are exactly the seven four-point neighborhoods. The line signatures are exactly the seven singleton line indicators. This conclusion fixes signatures on singletons and allows arbitrary monotone values on other side inputs consistent with those signatures.

Run `python verify_unique.py` to reproduce the deductions using only the standard library.

[The equality case](equality.md) needs exactly 34 total residual gates when it uses 13 mixed gates. Any 33-gate solution would therefore need at least 14 mixed gates.
