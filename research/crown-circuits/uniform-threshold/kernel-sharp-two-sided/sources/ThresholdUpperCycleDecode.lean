import ThresholdUpperCatalogue
namespace ThresholdUpperCatalogue
variable {V : Type*} [LinearOrder V]

private theorem not_diagonal (c d : V) (L : Finset V) (dc : d≠c)
    (nc : c∉L) (nd : d∉L) :
    ({c,d} : Finset V)∉spokes c L∪spokes d L := by
  intro hit
  rcases Finset.mem_union.mp hit with left | right
  · obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp left
    have hd : d∈({c,x} : Finset V) := eq.symm ▸ (by simp : d∈({c,d}: Finset V))
    rcases Finset.mem_insert.mp hd with same|sx
    · exact dc same
    · exact nd ((Finset.mem_singleton.mp sx).symm ▸ hx)
  · obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp right
    have hc : c∈({d,x} : Finset V) := eq.symm ▸ (by simp : c∈({c,d}: Finset V))
    rcases Finset.mem_insert.mp hc with same|sx
    · exact dc same.symm
    · exact nc ((Finset.mem_singleton.mp sx).symm ▸ hx)

/-- On its four vertices, the name can be recovered by testing the three
edges from the anchor. Its opposite is the unique candidate omitted. -/
theorem cycle_opposite (Q : Finset V) (d x : V) (h : d∈opposites Q)
    (hx : x∈opposites Q) :
    ({anchor Q d,x} : Finset V)∉cycle (⟨Q,d⟩ : CycleName V) ↔ x=d := by
  classical
  by_cases non : Q.Nonempty
  · let c := Q.min' non
    have hd : d∈Q.erase c := by simpa [opposites,non,c] using h
    have xx : x∈Q.erase c := by simpa [opposites,non,c] using hx
    let L := (Q.erase c).erase d
    have dc := (Finset.mem_erase.mp hd).1
    have nc : c∉L := fun m => Finset.notMem_erase c Q ((Finset.erase_subset _ _) m)
    have nd : d∉L := Finset.notMem_erase _ _
    have ac : anchor Q d=c := by simp [anchor,non,c]
    have acyc : cycle (⟨Q,d⟩ : CycleName V)=spokes c L∪spokes d L := by simp [cycle,ac,L]
    rw [ac,acyc]
    constructor
    · intro miss
      by_contra xd
      exact miss (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨x,Finset.mem_erase.mpr ⟨xd,xx⟩,rfl⟩))
    · rintro rfl
      exact not_diagonal c _ L dc nc nd
  · simp [opposites,non] at h

/-- Two different choices of opposite on a fixed support never collapse. -/
theorem cycle_separates (Q : Finset V) (a b : V) (ha : a∈opposites Q) (hb : b∈opposites Q)
    (eq : cycle (⟨Q,a⟩ : CycleName V)=cycle (⟨Q,b⟩ : CycleName V)) : a=b := by
  classical
  by_cases non : Q.Nonempty
  · have ac : anchor Q a=anchor Q b := by simp [anchor,non]
    have miss := (cycle_opposite Q a a ha ha).2 rfl
    rw [eq,ac] at miss
    exact (cycle_opposite Q b a hb ha).1 miss
  · simp [opposites,non] at ha

end ThresholdUpperCatalogue
