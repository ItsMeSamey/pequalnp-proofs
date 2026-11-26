# A kernel-checked threshold-two lower bound

For every n≥2 and every binary monotone circuit C computing ordinary threshold two on the full Boolean cube, Lean proves

    C.size ≥ 2n + (4/3)√(n+3) − 6.

The public theorem has exactly the arity, monotonicity and full-cube computation hypotheses. The proof derives the structural conditions for its intermediate graph arguments. The native step, squared bound and real-valued endpoint each report propext, Classical.choice and Quot.sound.

[Public theorem](sources/ThresholdPublicFourThirds.lean) · [Axiom receipt](axioms.log) · [Source order and checksums](ThresholdPublicFourThirds-manifest.tsv)

The package contains all 92 manifest-listed local and project sources. The replay script requires the pinned Lean 4.36 project and its compiled dependencies. The producer compiled the individual modules and final endpoint. The portable script has been syntax-checked. The sharper third-order asymptotic formula remains mathematically reviewed.

An independent verifier subsequently extracted the frozen package directly from Git and rebuilt all 92 modules, including all six PEqualNP project modules. Each local dependency resolved to a freshly built object from the same run. The native step, squared bound and real bound reproduced the three standard-axiom reports byte-for-byte. [Independent replay and environment](independent-replay/README.md) · [Final receipt](independent-replay/receipt.json)
