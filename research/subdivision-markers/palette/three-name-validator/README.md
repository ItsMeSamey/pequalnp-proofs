# Executable three-name certificate validator

Call `ThreeNameValidator.validate input certificate` to check a typed certificate. It returns true when the submitted decision is certified. The positive constructor claims an original support exists. The pin-conflict, outside and star constructors claim none exists. The theorem `ThreeNameValidator.sound` requires only successful Boolean validation.

For signed integer lists, `ThreeNameDense.check input certificate` returns `some true` for certified existence, `some false` for certified absence, and `none` on decoding or validation failure. It checks physical name independence, lengths, signed word and index bounds, and uniqueness of set and attachment fields. Original columns retain order and multiplicity.

A star certificate supplies pivot rows with original supporting labels, initial columns, three root labels, ordinary-to-padded attachment, successive frames with interface tables and projection rows, and a final graph with forward and reverse matrices. The validator computes pivot correctness, named-root consistency, injectivity and original-column agreement. Each transition is checked against its preceding frame. The terminal checks the depicted endpoints, both labeled linear maps and a shared center. There are no semantic proof fields in the certificate.

Positive, conflict and outside branches compute original witness and parity checks directly. Soundness quantifies over original supports containing the pins. For signed records the conclusion applies to decoded literal input. The package uses no external graph recognizer or Boolean oracle. Producer completeness and evaluation complexity remain separate. OPERATIONS.md gives direct comparison counts.

The main function in lean/ThreeNameDenseControls.lean runs accepted and malformed signed-input controls, including a genuine split. The other controls use kernel reduction of the proof-free interface.
