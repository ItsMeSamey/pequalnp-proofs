import Q1DoubleFourPatterns
import Q1PrivateTight

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

/-- Connect the literal Y occurrences to the four-slot exclusion without assuming
distinct supports, anchor identities, or a preselected transversal for any slot. -/
theorem physical_four {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (label : Pos → Fin n) (inj : Function.Injective label)
    (L : Fin 4 → Finset (Fin n)) (J : Finset (Fin 4))
    (hit : ∀ c i, label (i,false) ∈ L c ∨ label (i,true) ∈ L c)
    (clean : ∀ S : Finset (Fin n), (∀ c, ∃ v ∈ S, v ∈ L c) → ∃ x ∈ S, ∃ y ∈ S, G.Adj x y)
    (indep : ∀ x y, ¬ G.Adj (label (false,x)) (label (true,y)))
    (edge : ∀ i k, G.Adj (label (i,k)) (label (i,!k)))
    (res : ∀ i k, s(label (i,k),label (i,!k)) ∈ Ustar G C)
    (anchor : ∀ c, ∀ x ∈ L c, ∀ y ∈ L c, x ≠ y →
      ∃ w, ∀ z ∈ L c, G.Adj w z ∧ s(w,z) ∈ starEdges G C) :
    ∃ T : Finset Pattern, T.card=J.card ∧ ∀ a b, (∀ j ∈ J, a ∈ L j ∨ b ∈ L j) →
      ∀ t ∈ T, inSlot label t a ∨ inSlot label t b := by
  classical
  have sep (x y : Bool) : label (false,x) ≠ label (true,y) :=
    fun eq => by simpa using congrArg Prod.fst (inj eq)
  have pair := Private.tight_clause four (fun i k => label (i,k)) L hit clean indep sep edge res anchor
  have reject (t : Pattern) : ∃ c, label (false,!t.1) ∉ L c ∧ label (true,!t.2) ∉ L c := by
    by_contra! allMeet
    let a := label (false,!t.1)
    let b := label (true,!t.2)
    have meets (c : Fin 4) : a ∈ L c ∨ b ∈ L c := by
      by_cases ha : a ∈ L c
      · exact Or.inl ha
      · exact Or.inr (allMeet c ha)
    obtain ⟨u,hu,v,hv,adj⟩ := clean {a,b} (fun c => by
      rcases meets c with h | h
      · exact ⟨a,by simp,h⟩
      · exact ⟨b,by simp,h⟩)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.irrefl adj
    · exact indep _ _ adj
    · exact indep _ _ adj.symm
    · exact G.irrefl adj
  obtain ⟨f,hf⟩ := physical_patterns label inj L pair hit reject
  exact shared_patterns L f hf J

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
