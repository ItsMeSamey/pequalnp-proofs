import Research.PuncturedFanoMarkerPacking

namespace PuncturedFanoMarkers

def silentProducts (f : List Nat) : List Nat :=
  ((rawConjunctions.flatMap fun r => (products f).map fun m => r &&& m).filter
    fun c => c &&& negativeMask == 0).eraseDups

def productCoverageCheck : Bool := families.all fun f => (silentProducts f).all fun c =>
  (largeCharges f).contains c || decide ((edgeSet c).card ≤ 1)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem product_coverage_checked : productCoverageCheck = true := by decide

/-- Model a charging gate by a single raw conjunction times some of the
available OR markers. Require silence on all critical negatives, and permit
the gate to be assigned an arbitrary subset of its accepted positive edges. -/
theorem raw_gate_cover_bound (f : List Nat) (hf : f ∈ families)
    (charges : Finset (Finset Nat))
    (allowed : ∀ A ∈ charges, ∃ r ∈ rawConjunctions, ∃ m ∈ products f,
      (r &&& m) &&& negativeMask = 0 ∧ A ⊆ edgeSet (r &&& m))
    (covers : Finset.range 18 ⊆ charges.biUnion id) : 16 ≤ charges.card := by
  apply charge_cover_lower_bound f hf charges _ covers
  intro A hA
  obtain ⟨r,hr,m,hm,hs,sub⟩ := allowed A hA
  have mem : r &&& m ∈ silentProducts f := by
    simp only [silentProducts,List.mem_eraseDups,List.mem_filter,List.mem_flatMap,List.mem_map,
      beq_iff_eq]
    exact ⟨⟨r,hr,m,hm,rfl⟩,hs⟩
  have valid := List.all_eq_true.mp (List.all_eq_true.mp product_coverage_checked f hf) _ mem
  simp only [Bool.or_eq_true,List.contains_iff_mem,decide_eq_true_eq] at valid
  rcases valid with large | single
  · exact Or.inr ⟨_,large,sub⟩
  · exact Or.inl ((Finset.card_le_card sub).trans single)

end PuncturedFanoMarkers
