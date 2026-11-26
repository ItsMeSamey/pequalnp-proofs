import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace DeletionPacking

theorem union_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : α → Finset β) (k : ℕ) (S : Finset α)
    (sizes : ∀ a ∈ S, k ≤ (F a).card)
    (overlap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ((F a) ∩ (F b)).card ≤ 1) :
    2*k*S.card + S.card ≤ 2*(S.biUnion F).card + S.card^2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have sub : S ⊆ insert a S := Finset.subset_insert _ _
    have prev := ih (fun b hb => sizes b (sub hb))
      (fun b hb c hc => overlap b (sub hb) c (sub hc))
    have own := sizes a (by simp)
    have inter : (F a ∩ S.biUnion F).card ≤ S.card := by
      rw [Finset.inter_biUnion]
      simpa using Finset.card_biUnion_le_card_mul S (fun b => F a ∩ F b) 1
        (fun b hb => overlap a (by simp) b (sub hb) (fun e => ha (e ▸ hb)))
    have total := Finset.card_union_add_card_inter (F a) (S.biUnion F)
    rw [Finset.card_insert_of_notMem ha,Finset.biUnion_insert]
    have square : (S.card + 1)^2 = S.card^2 + 2*S.card + 1 := by ring
    rw [square,Nat.mul_add,Nat.mul_one]
    omega

theorem few_depleted {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : α → Finset β) (D : Finset β) (S : Finset α) (q : ℕ)
    (size : 2 * D.card < q^2+q)
    (many : ∀ a ∈ S, q ≤ (F a ∩ D).card)
    (overlap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (F a ∩ F b).card ≤ 1) :
    S.card < q := by
  by_contra! h
  obtain ⟨T,sub,card⟩ := Finset.exists_subset_card_eq h
  let G := fun a => F a ∩ D
  have small := union_bound G q T (fun a ha => many a (sub ha)) (by
    intro a ha b hb ne
    apply le_trans (Finset.card_le_card ?_) (overlap a (sub ha) b (sub hb) ne)
    exact Finset.inter_subset_inter Finset.inter_subset_left Finset.inter_subset_left)
  have covered : T.biUnion G ⊆ D := by
    intro v hv
    obtain ⟨_,_,inc⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_inter.mp inc).2
  have := Finset.card_le_card covered
  rw [card] at small
  have e : 2*q*q = 2*(q^2) := by ring
  rw [e] at small
  omega

end DeletionPacking
