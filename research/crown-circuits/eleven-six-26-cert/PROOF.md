# Eleven-input threshold two has minimum size 27 with at most six ANDs

Every binary monotone AND/OR circuit with at most six AND gates computing threshold two on eleven inputs needs at least 27 total gates. Depth and fanout are unrestricted. The included circuit has 27 gates and four ANDs. It passes all 2,048 assignments.

The five-AND floor was previously established. For size 26 and six ANDs, backend.md proves the switch transfer and finite exclusion. The eleven-label signed universe contains 41,565 profiles. q1 has a full chronology replay for 16,118 profiles. For q2..5, minimum-dirty single-branch cancellation removes every profile with a nonfull activation omitting at most two observable atoms. Every remaining profile is covered by its helper ledger. Two q2 and five q3 hits in the relaxed search fail separate exact chronological/heat checks; q4 and q5 have zero relaxed hits.

Independent verification and reductions researchers checked the substitutions, sparse transfer, signed action, pointwise stabilizer, and chronological forest mapping. Reductions independently reconstructed all 277 q4 and 40 q5 IDs and their 53,193,416 and 69,188,813 recorded visits, checked every contributing source, replayed the all-clean calculation, and verified the constructive bound. This is a finite computational proof without a Lean certificate. Higher AND counts require separate arguments.
