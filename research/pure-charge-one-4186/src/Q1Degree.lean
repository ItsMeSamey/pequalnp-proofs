import Q0Matching

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q0

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {clauses : Finset (Finset (Fin n))} {E A B : Finset (Fin n)} {h u v : Fin n}

private theorem clash {K : Finset (Fin n)} (four : NoFourCycle G)
    {x y : Fin n} (xy : x ≠ y) (hx : G.Adj h x) (hy : G.Adj h y)
    (res : s(h,x) ∈ Ustar G C) (kx : x ∈ K) (ky : y ∈ K)
    (anch : ∃ w, ∀ z ∈ K, G.Adj w z ∧ s(w,z) ∈ starEdges G C) : False := by
  obtain ⟨w, hw⟩ := anch
  have eq : w = h := by
    by_contra wh
    exact xy (Finset.card_le_one.mp (four w h wh) x
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw x kx).1, hx⟩) y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw y ky).1, hy⟩))
  exact (Finset.mem_sdiff.mp res).2 (eq ▸ (hw x kx).2)

theorem degree_exception (four : NoFourCycle G) (anchor : clauseStars G C (clauses.erase E))
    (clean : ∀ x y, hitsPair clauses x y → G.Adj x y)
    (hu : hitsPair clauses h u) (hv : hitsPair clauses h v)
    (ru : s(h,u) ∈ Ustar G C) (_rv : s(h,v) ∈ Ustar G C) (uv : u ≠ v) :
    E ∈ clauses ∧ h ∉ E ∧ u ∈ E ∧ v ∈ E ∧
      (∀ K ∈ clauses.erase E, h ∈ K) ∧ ∀ z ∈ E, G.Adj h z := by
  classical
  have other (K : Finset (Fin n)) (hK : K ∈ clauses.erase E) : h ∈ K := by
    by_contra miss
    have ku := (hu K (Finset.mem_of_mem_erase hK)).resolve_left miss
    have kv := (hv K (Finset.mem_of_mem_erase hK)).resolve_left miss
    exact clash four uv (clean _ _ hu) (clean _ _ hv) ru ku kv (anchor K hK u ku v kv uv)
  have omitted : ∃ K ∈ clauses, h ∉ K := by
    by_contra! all
    exact G.loopless.irrefl h (clean h h (fun K hk => Or.inl (all K hk)))
  obtain ⟨K,hK,miss⟩ := omitted
  have eq : K = E := by
    by_contra neq
    exact miss (other K (Finset.mem_erase.mpr ⟨neq,hK⟩))
  subst K
  refine ⟨hK,miss,(hu E hK).resolve_left miss,(hv E hK).resolve_left miss,other,?_⟩
  intro z hz
  apply clean
  intro K hk
  by_cases he : K = E
  · subst K; exact Or.inr hz
  · exact Or.inl (other K (Finset.mem_erase.mpr ⟨he,hk⟩))

theorem degree_children (four : NoFourCycle G) (anchor : clauseStars G C (clauses.erase E))
    (clean : ∀ x y, hitsPair clauses x y → G.Adj x y)
    (hu : hitsPair clauses h u) (hv : hitsPair clauses h v)
    (ru : s(h,u) ∈ Ustar G C) (rv : s(h,v) ∈ Ustar G C) (uv : u ≠ v)
    (split : E = A ∪ B) (children : clauseStars G C {A,B}) :
    E = {u,v} ∧ ((A = {u} ∧ B = {v}) ∨ (A = {v} ∧ B = {u})) := by
  classical
  obtain ⟨_,_,ue,ve,_,adj⟩ := degree_exception four anchor clean hu hv ru rv uv
  have single (K : Finset (Fin n)) (hk : K ∈ ({A,B} : Finset _))
      (sub : K ⊆ E) (x : Fin n) (mem : x ∈ K) (res : s(h,x) ∈ Ustar G C) : K = {x} := by
    apply Finset.ext
    intro y
    rw [Finset.mem_singleton]
    constructor
    · intro hy
      by_contra ne
      exact clash four (Ne.symm ne) (adj x (sub mem)) (adj y (sub hy)) res mem hy
        (children K hk x mem y hy (Ne.symm ne))
    · rintro rfl; exact mem
  have subA : A ⊆ E := by rw [split]; exact Finset.subset_union_left
  have subB : B ⊆ E := by rw [split]; exact Finset.subset_union_right
  have bySide (x : Fin n) (xe : x ∈ E) (res : s(h,x) ∈ Ustar G C) : A = {x} ∨ B = {x} := by
    rw [split, Finset.mem_union] at xe
    exact xe.elim (fun ha => Or.inl (single A (by simp) subA x ha res))
      (fun hb => Or.inr (single B (by simp) subB x hb res))
  have pair : (A = {u} ∧ B = {v}) ∨ (A = {v} ∧ B = {u}) := by
    have ne : ({u} : Finset _) ≠ {v} := by simpa using uv
    rcases bySide u ue ru with au | bu <;> rcases bySide v ve rv with av | bv
    · exact False.elim (ne (au.symm.trans av))
    · exact Or.inl ⟨au,bv⟩
    · exact Or.inr ⟨av,bu⟩
    · exact False.elim (ne (bu.symm.trans bv))
  refine ⟨?_,pair⟩
  rcases pair with ⟨au,bv⟩ | ⟨av,bu⟩
  · simp [split,au,bv]
  · ext z; simp [split,av,bu,or_comm]

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
