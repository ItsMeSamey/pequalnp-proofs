import Research.BoundedOccurrence

namespace HallBackdoor

variable {C V : Type*} [Fintype C] [DecidableEq V]

/-- Projection onto B is exact. Clauses outside the core retain at least three
distinct variables outside B. Only the outside incidences have a degree bound. -/
theorem exactProjection (vars : C → Finset V) (sign : C → V → Bool)
    (B : Finset V)
    (width : ∀ c, ¬ vars c ⊆ B → 3 ≤ (vars c \ B).card)
    (degree : ∀ v : V, v ∉ B →
      (Finset.univ.filter (fun c => v ∈ vars c)).card ≤ 3)
    (seed : V → Bool) :
    (∀ c, vars c ⊆ B → ∃ v ∈ vars c, seed v = sign c v) ↔
    ∃ a : V → Bool, (∀ v ∈ B, a v = seed v) ∧
      ∀ c, ∃ v ∈ vars c, a v = sign c v := by
  classical
  constructor
  · intro hcore
    let R := {c : C // ¬ vars c ⊆ B}
    let residual := fun c : R => vars c.val \ B
    have deg : ∀ v : V, (Finset.univ.filter (fun c : R => v ∈ residual c)).card ≤ 3 := by
      intro v
      by_cases hv : v ∈ B
      · simp [residual, hv]
      · apply le_trans _ (degree v hv)
        apply Finset.card_le_card_of_injOn (fun c : R => c.val)
        · intro c hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp
            (Finset.mem_filter.mp hc).2).1⟩
        · intro c _ d _ heq
          exact Subtype.ext heq
    obtain ⟨outside, hout⟩ := BoundedOccurrence.satisfiable residual
      (fun c => sign c.val) (fun c => width c.val c.property) deg
    refine ⟨fun v => if v ∈ B then seed v else outside v, ?_, ?_⟩
    · intro v hv
      simp [hv]
    · intro c
      by_cases h : vars c ⊆ B
      · obtain ⟨v, hv, heq⟩ := hcore c h
        exact ⟨v, hv, by simpa [h hv] using heq⟩
      · obtain ⟨v, hv, heq⟩ := hout ⟨c, h⟩
        obtain ⟨hin, hnot⟩ := Finset.mem_sdiff.mp hv
        exact ⟨v, hin, by simpa [hnot] using heq⟩
  · rintro ⟨a, agrees, sat⟩ c hc
    obtain ⟨v, hv, heq⟩ := sat c
    exact ⟨v, hv, (agrees v (hc hv)).symm.trans heq⟩

/-- A precomputed matching suffices even for mixed clauses with only one
variable outside B. Its verification and construction are independent of seed. -/
theorem exactProjectionOfMatching (vars : C → Finset V) (sign : C → V → Bool)
    (B : Finset V)
    (f : {c : C // ¬ vars c ⊆ B} → V) (inj : Function.Injective f)
    (hit : ∀ c, f c ∈ vars c.val \ B) (seed : V → Bool) :
    (∀ c, vars c ⊆ B → ∃ v ∈ vars c, seed v = sign c v) ↔
    ∃ a : V → Bool, (∀ v ∈ B, a v = seed v) ∧
      ∀ c, ∃ v ∈ vars c, a v = sign c v := by
  classical
  constructor
  · intro core
    let a := fun v => if h : ∃ c, f c = v then sign h.choose.val v else seed v
    have agrees : ∀ v ∈ B, a v = seed v := by
      intro v hv
      have h : ¬ ∃ c, f c = v := by
        rintro ⟨c, rfl⟩
        exact (Finset.mem_sdiff.mp (hit c)).2 hv
      exact dite_eq_right h
    refine ⟨a, agrees, fun c => ?_⟩
    by_cases h : vars c ⊆ B
    · obtain ⟨v, hv, heq⟩ := core c h
      exact ⟨v, hv, (agrees v (h hv)).trans heq⟩
    · let d : {c : C // ¬ vars c ⊆ B} := ⟨c, h⟩
      have hd : ∃ e, f e = f d := ⟨d, rfl⟩
      exact ⟨f d, (Finset.mem_sdiff.mp (hit d)).1, by simp only [a, dite_eq_left hd, inj hd.choose_spec, d]⟩
  · rintro ⟨a, agrees, sat⟩ c hc
    obtain ⟨v, hv, heq⟩ := sat c
    exact ⟨v, hv, (agrees v (hc hv)).symm.trans heq⟩

end HallBackdoor
