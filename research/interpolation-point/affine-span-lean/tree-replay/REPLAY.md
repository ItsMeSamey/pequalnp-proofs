# Replay

This incremental verifier uses the previously sealed charged and indexed receipts. Expected SHA-256 digests and compiler hash appear in replay.py. Recreate those artifacts if their object directories have been retired.

On an exclusively assigned Lean slot, copy this evidence directory beside the baseline verifier directories. Choose an empty tmpfs directory, write its path in workdir and extract the fixed Git tree into it:

    git -C /workspace/pnp-research archive ec21602f9f090c2aeb9b7d60268bbcbb3c7c0775:research/interpolation-point/affine-span-lean | tar -x -C "$fresh_root"

Create an empty file named continue beside replay.py for an uninterrupted run. The original review instead paused at module 15 for an authorized compiler handoff. Run python replay.py, then python extra_controls.py and python width_control.py. The first runner checks the 98-source and 39-source locks, prior objects, actual project imports for the new modules, every new object and log against its producer receipt, and a dedicated axiom probe. The second checks six-site controls and eight named interface, cost and equivalence reports. The standalone Python control checks high private rank on six additional instances.

Dependency revisions are in dependencies.json. Temporary directory names record the paths resolved on this run.
