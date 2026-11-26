# Fourteen inputs and nine AND gates

A binary monotone circuit with unrestricted fanout that computes threshold two on fourteen inputs cannot have size 34 with nine AND gates. The result closes one gate composition at this size.

The proof begins with the two-reader regularization and the layer bound. At size 34 the 13-input lower bound forces the regular representative. The 25 available OR gates give a receiver decoder budget of q−3 on q flags. The following files give the proof in order.

1. [Small branching groups](degree/t14-34/small-branches.md) and [degree cap](degree/t14-34/degree-cap.md) characterize the candidates for branching and bound the maximum receiver degree by four.
2. [Receiver layers](geometry/eleven27-seven/receiver-layers.md) supplies the component and isolated-pure counting argument. [Quartet separation](geometry/fourteen34/nine-and-quartets.md) and [the unique quartic flag](geometry/fourteen34/sole-quartic.md) reduce the problem to one possible branching quartet.
3. [The remote fork](geometry/fourteen34/remote-fork.md) excludes its three-component hosts. [The remaining partitions](geometry/fourteen34/nine-and-completion.md) finish the four-or-more-component cases and the circuit with no branching.

The published dependencies are copied from commit f66f5c73f2a5e471ce4cc9a588fc2fbdb2f533d5 of the research fork under their original research/crown-circuits paths. The proof uses [C(13)=32](research/crown-circuits/thirteen-exact/README.md), [C(12)=29](research/crown-circuits/threshold-twelve-final-cert/README.md), [C(11)=27](research/crown-circuits/eleven-unrestricted-27-cert/README.md) and [C(10)=24](research/crown-circuits/ten-exact-cert/PROOF.md). Earlier eight- and nine-input packages are included for the induction underlying the [secondary minimum at the OR floor](degree/t13-31/or-optimal.md). The regularization, dark-gate accounting, and early-injection star inequality are given in the verification/threshold-twelve files and [raw reader reduction](degree/t13-31/ten-tight.md). All proofs use the binary monotone AND/OR circuit model.

Run the two manifests from this directory.

    sha256sum -c SHA256SUMS
    sha256sum -c geometry/fourteen34/a9-sha256.txt

[Independent reviews](REVIEW.md) cover the four newly written component and assembly proofs. No new finite search or end-to-end Lean proof is required or claimed.
