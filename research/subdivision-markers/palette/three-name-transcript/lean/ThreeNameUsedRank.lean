import ThreeNameIncidenceRank
import ThreeNameIncidence

namespace ThreeNameIncidenceRank
open scoped BigOperators
variable {E V : Type*} [DecidableEq E] [DecidableEq V]

/-- The ambient edge and vertex types need not be finite; only the support
and its used endpoints enter the bound. -/
theorem used_card_bound (tail head : E → V) (C : Finset E)
    (hc : ThreeNameSplitCircuit.Circuit (incidence tail head) C) :
    C.card ≤ (C.image tail ∪ C.image head).card := by
  let U := C.image tail ∪ C.image head
  let l : C → U := fun e => ⟨tail e, Finset.mem_union_left _ (Finset.mem_image_of_mem _ e.property)⟩
  let r : C → U := fun e => ⟨head e, Finset.mem_union_right _ (Finset.mem_image_of_mem _ e.property)⟩
  have val_eq (e : C) (v : U) :
      incidence l r e v = incidence tail head e.val v.val := by
    simp only [incidence, l, r, Subtype.ext_iff]
  have lift_eq (S : Finset C) (v : U) :
      (∑ e ∈ S.image Subtype.val, incidence tail head e) v.val =
        (∑ e ∈ S, incidence l r e) v := by
    rw [Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)]
    simp only [Finset.sum_apply, val_eq]
  have whole : Finset.univ.image (Subtype.val : C → E) = C := Finset.attach_image_val
  have subcirc : ThreeNameSplitCircuit.Circuit (incidence l r) Finset.univ := by
    obtain ⟨e,he⟩ := hc.1
    refine ⟨⟨⟨e,he⟩,Finset.mem_univ _⟩, ?_, ?_⟩
    · funext v
      rw [← lift_eq, whole, hc.2.1]
      rfl
    · intro S _ hs hz
      let T := S.image (Subtype.val : C → E)
      have sub : T ⊆ C := by
        intro x hx
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
        exact a.property
      have orig : (∑ e ∈ T, incidence tail head e) = 0 := by
        funext v
        by_cases hv : v ∈ U
        · exact (lift_eq S ⟨v,hv⟩).trans (congrFun hz ⟨v,hv⟩)
        · rw [Finset.sum_apply]
          apply Finset.sum_eq_zero
          intro a ha
          have h₁ : v ≠ tail a := fun h => hv (h ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem _ (sub ha)))
          have h₂ : v ≠ head a := fun h => hv (h ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ (sub ha)))
          simp [incidence, h₁, h₂]
      have allT := hc.2.2 T sub (hs.image _) orig
      apply Finset.eq_univ_of_forall
      intro a
      have ha : a.val ∈ T := allT.symm ▸ a.property
      obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha
      exact Subtype.ext hba ▸ hb
  simpa only [Fintype.card_coe] using incidence_card_le l r subcirc

/-- A minimal binary incidence dependence cannot contain three distinct
edge positions incident at a common vertex, including in a multigraph. -/
theorem circuit_excludes_three (l r : E → V) (C : Finset E)
    (hc : ThreeNameSplitCircuit.Circuit (incidence l r) C)
    (x : V) (a b d : E) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (included : ({a,b,d} : Finset E) ⊆ C)
    (ha : l a = x ∨ r a = x) (hb : l b = x ∨ r b = x) (hd : l d = x ∨ r d = x) :
    False := by
  have same (e : E) (v : V) :
      (ThreeNameIncidence.ends l r e v : ZMod 2) = incidence l r e v := by
    by_cases h : v = l e <;> by_cases j : v = r e <;>
      simp [ThreeNameIncidence.ends, incidence, h, j, Nat.cast_add]
  have cycle := ThreeNameIncidence.cycle_of_zero_sum l r C (fun v => by
    simpa only [same, Finset.sum_apply, Pi.zero_apply] using congrFun hc.2.1 v)
  have excess := ThreeNameIncidence.strict_excess l r C cycle x a b d hab had hbd included ha hb hd
  rw [ThreeNameIncidence.handshake] at excess
  exact (Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 (used_card_bound l r C hc))) excess

#print axioms circuit_excludes_three
#print axioms used_card_bound
end ThreeNameIncidenceRank
