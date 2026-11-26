# Fourteen-input threshold two at size 34 with eight ANDs

In a raw-regular, clean-terminal circuit in this stratum, every receiver has at most four incident raw labels. If the receiver graph is connected its maximum degree is at most three. At most one pure two-label receiver may branch. These are structural constraints on any candidate circuit.

The principal argument is in geometry/fourteen34/eight-and-high-degree.md. Its signed digest is ac2342f1ba3c687453e8cb67940bad095451e4ff2f89b173c9ab7ec278e4619d. The degree/t14-34 notes supply the prerequisite branching and restriction arguments. Some supporting notes study nine ANDs. The principal proof identifies the individual arguments transplanted to eight ANDs and recalculates the decoder budget.

This is a source-reviewed mathematical proof. It uses the project's exact smaller-input gate minima, optimal AND counts at the OR minimum, raw and clean-terminal normalization, and the receiver layer argument. It does not settle existence at eight ANDs. To verify the frozen text, run sha256sum -c SHA256SUMS from this directory.
