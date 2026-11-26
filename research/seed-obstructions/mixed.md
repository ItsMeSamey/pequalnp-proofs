# Exact mixed-gate complexity of the residual

Treat every monotone function of the 13 point bits and every monotone function of the seven remaining line bits as free inputs. The minimum number of additional binary monotone gates that separates the residual positives from the sampled negatives is **13**. This is also the exact minimum number of mixed gates in an ordinary residual circuit when a gate with ancestors from both sides is counted as mixed.

The certificate supplies seven ordered positive/negative pairs for each side, indexed in the 676 columns of the published theorem. For a point pair, its positive line vector is contained in its negative line vector. Thus only a point-side signal can be 1 at the positive and 0 at the negative. Furthermore, for every two point pairs, the positive point vector of one is contained in the negative point vector of the other. No monotone point function can distinguish both. The same two checks hold after interchanging points and lines for the seven line pairs.

Any monotone separator must use at least one distinguishing boundary signal per pair. The 14 pairs require 14 distinct signals. The connected output cone with those signals as leaves therefore contains at least 13 binary gates. Treating the outputs of all point-only and line-only gates as freely available sources proves the claim for arbitrary interleaved circuits with sharing. For equality use each of the seven line bits AND its four-point incidence OR, followed by six OR gates. The verifier checks that construction on all 676 columns, including the erased ones.

Run `python verify_mixed.py` from this directory. The raw decoder uses the original formal statement and the Python standard library. The full 34-gate existence question remains open.
