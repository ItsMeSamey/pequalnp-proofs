# A 16-charge packing on the punctured Fano test set

The test set has 18 positive incidence edges and 19 maximal negative inputs. The left bits index the seven points. The right bits index lines 0, 2, 3, 4, 5, 6 in that order. A marker candidate is the OR of two distinct raw inputs. Two candidates are compatible if they are never simultaneously true on a listed negative.

The Lean theorem `PuncturedFanoMarkers.compatible_set_charge_bound` certifies that any pairwise compatible set of candidates fits one of 94 enumerated families. In that family, a cover of the 18 edge indices needs at least 16 different charges. Each permitted charge is one edge, or a subset of a larger set supplied by a raw conjunction intersected with a product of markers, false on all 19 negatives. All 88 distinct raw conjunction signatures on the tests are included.

The proof computes a family-dependent packing of at least 16 edge indices. Each allowed charge intersects the packing at most once. The numerical certificates are verified with Lean's `decide`.

Applying this bound to an arbitrary size-22 circuit with nine OR gates also requires a structural theorem translating the circuit's execution into the specified marker families and charges. That translation is a separate mathematical argument. This file proves the finite packing component.

[The raw-gate cover theorem](../../lean/Research/PuncturedFanoRawGateCover.lean) derives the same 16-charge bound when a charge is contained in the positive support of a raw conjunction times a marker subset-product that vanishes on all 19 critical negatives. It removes the additional assumption that a small charge covers at most one cell.
