import Q0Matching

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q0

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {clauses : Finset (Finset (Fin n))} {E : Finset (Fin n)}

private theorem incompatible (four : NoFourCycle G) (anchor : clauseStars G C (clauses.erase E))
    {K : Finset (Fin n)} (mem : K ∈ clauses.erase E) {x p y : Fin n}
    (ne : p ≠ y) (xp : G.Adj x p) (xy : G.Adj x y) (res : s(x,p) ∈ Ustar G C) :
    ¬ (p ∈ K ∧ y ∈ K) := by
  rintro ⟨hp, hy⟩
  obtain ⟨w, hw⟩ := anchor K mem p hp y hy ne
  have eq : w = x := by
    by_contra h
    apply ne
    apply Finset.card_le_one.mp (four w x h) p _ y _
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw p hp).1, xp⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw y hy).1, xy⟩
  exact (Finset.mem_sdiff.mp res).2 (eq ▸ (hw p hp).2)

/-- Any two disjoint accepted residual edges have no ambient cross edge.
The exceptional support need not occur in the clause set. -/
theorem matching_induced (four : NoFourCycle G) (anchor : clauseStars G C (clauses.erase E))
    (clean : ∀ u v, hitsPair clauses u v → G.Adj u v)
    {x p y q : Fin n} (hx : hitsPair clauses x p) (hy : hitsPair clauses y q)
    (rx : s(x,p) ∈ Ustar G C) (ry : s(y,q) ∈ Ustar G C)
    (hxy : x ≠ y) (hpy : p ≠ y) (hqx : q ≠ x) (hpq : p ≠ q) : ¬ G.Adj x y := by
  classical
  intro cross
  have ordinary : (clauses.erase E).Nonempty := by
    by_contra none
    have only (K : Finset (Fin n)) (hK : K ∈ clauses) : K = E := by
      by_contra ne
      exact none ⟨K, Finset.mem_erase.mpr ⟨ne,hK⟩⟩
    by_cases ex : x ∈ E
    · apply G.loopless.irrefl x
      apply clean x x
      intro K hK
      rw [only K hK]
      exact Or.inl ex
    · apply G.loopless.irrefl p
      apply clean p p
      intro K hK
      have h := hx K hK
      rw [only K hK] at h ⊢
      exact Or.inl (h.resolve_left ex)
  have xp := clean _ _ hx
  have yq := clean _ _ hy
  have rp : s(p,x) ∈ Ustar G C := Sym2.eq_swap (a := x) (b := p) ▸ rx
  have rq : s(q,y) ∈ Ustar G C := Sym2.eq_swap (a := y) (b := q) ▸ ry
  have splitClause {K : Finset (Fin n)} (hK : K ∈ clauses.erase E) :
      (x ∈ K ∧ y ∈ K) ∨ (p ∈ K ∧ q ∈ K) := by
    have h1 := incompatible four anchor hK hpy xp cross rx
    have h2 := incompatible four anchor hK hqx yq cross.symm ry
    have h3 := hx K (Finset.mem_of_mem_erase hK)
    have h4 := hy K (Finset.mem_of_mem_erase hK)
    tauto
  have extra : G.Adj x q ∨ G.Adj p y := by
    by_cases ex : x ∈ E
    · left
      apply clean
      intro K hK
      by_cases eq : K = E
      · exact Or.inl (by simpa [eq] using ex)
      · rcases splitClause (Finset.mem_erase.mpr ⟨eq,hK⟩) with hh | hh
        · exact Or.inl hh.1
        · exact Or.inr hh.2
    · right
      apply clean
      intro K hK
      by_cases eq : K = E
      · subst K
        exact Or.inl ((hx E hK).resolve_left ex)
      · rcases splitClause (Finset.mem_erase.mpr ⟨eq,hK⟩) with hh | hh
        · exact Or.inr hh.2
        · exact Or.inl hh.1
  obtain ⟨K,hK⟩ := ordinary
  have shape := splitClause hK
  rcases extra with xq | py
  · have h1 := incompatible four anchor hK hpq xp xq rx
    have h2 := incompatible four anchor hK hxy.symm yq.symm xq.symm rq
    tauto
  · have h1 := incompatible four anchor hK hxy xp.symm py rp
    have h2 := incompatible four anchor hK hpq.symm yq py.symm ry
    tauto

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
