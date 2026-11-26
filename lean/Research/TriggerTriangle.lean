import Mathlib.Data.Finset.Card

namespace CrownCollision
variable {V : Type*} [DecidableEq V]

/-- Private inputs of a gate with a common predecessor have cardinality at most one. -/
private theorem private_le_one (A : Finset V) (p : V) (hp : p ∈ A) (ha : A.card ≤ 2) :
    (A.erase p).card ≤ 1 := by
  rw [Finset.card_erase_of_mem hp]
  omega

/-- All but at most three read wires are common to the three OR gates. -/
theorem trigger_triangle (A B C : Finset V) (ha : A.card ≤ 2) (hb : B.card ≤ 2)
    (hc : C.card ≤ 2) (ab : (A ∩ B).Nonempty) (bc : (B ∩ C).Nonempty)
    (ca : (C ∩ A).Nonempty) :
    (((A ∪ B) ∪ C) \ ((A ∩ B) ∩ C)).card ≤ 3 := by
  obtain ⟨x,hx⟩ := ab
  obtain ⟨y,hy⟩ := bc
  obtain ⟨z,hz⟩ := ca
  obtain ⟨xa,xb⟩ := Finset.mem_inter.mp hx
  obtain ⟨yb,yc⟩ := Finset.mem_inter.mp hy
  obtain ⟨zc,za⟩ := Finset.mem_inter.mp hz
  by_cases common : ((A ∩ B) ∩ C).Nonempty
  · obtain ⟨p,hp⟩ := common
    obtain ⟨pab,pc⟩ := Finset.mem_inter.mp hp
    obtain ⟨pa,pb⟩ := Finset.mem_inter.mp pab
    have sub : ((A ∪ B) ∪ C) \ ((A ∩ B) ∩ C) ⊆ (A.erase p ∪ B.erase p) ∪ C.erase p := by
      intro t ht
      obtain ⟨hu, hn⟩ := Finset.mem_sdiff.mp ht
      have ne : t ≠ p := fun eq => hn (eq ▸ hp)
      simp only [Finset.mem_union] at hu ⊢
      simp only [Finset.mem_erase]
      tauto
    have s := Finset.card_le_card sub
    have s₁ := Finset.card_union_le (A.erase p) (B.erase p)
    have s₂ := Finset.card_union_le (A.erase p ∪ B.erase p) (C.erase p)
    have := private_le_one A p pa ha
    have := private_le_one B p pb hb
    have := private_le_one C p pc hc
    omega
  · have no : ∀ p, p ∈ A → p ∈ B → p ∈ C → False := fun p a b c =>
      common ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨a,b⟩,c⟩⟩
    have xy : x ≠ y := fun e => no x xa xb (e ▸ yc)
    have xz : x ≠ z := fun e => no x xa xb (e ▸ zc)
    have yz : y ≠ z := fun e => no y (e ▸ za) yb yc
    have pairEq (D : Finset V) (d : D.card ≤ 2) (i j : V) (ne : i ≠ j) (hi : i ∈ D) (hj : j ∈ D) :
        D = {i,j} := by
      symm
      exact Finset.eq_of_subset_of_card_le (by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption) (by simpa [ne] using d)
    have eA := pairEq A ha x z xz xa za
    have eB := pairEq B hb x y xy xb yb
    have eC := pairEq C hc y z yz yc zc
    have sub : ((A ∪ B) ∪ C) \ ((A ∩ B) ∩ C) ⊆ {x,y,z} := by
      rw [eA,eB,eC]
      intro t ht
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_insert,
        Finset.mem_singleton] at ht ⊢
      tauto
    exact (Finset.card_le_card sub).trans (by simp [xy,xz,yz])

theorem first_trigger_count (A B C F : Finset V) (ha : A.card ≤ 2) (hb : B.card ≤ 2)
    (hc : C.card ≤ 2) (ab : (A ∩ B).Nonempty) (bc : (B ∩ C).Nonempty)
    (ca : (C ∩ A).Nonempty) (readable : F ⊆ (A ∪ B) ∪ C)
    (cannot_fire_all : ∀ p ∈ F, p ∈ A → p ∈ B → p ∈ C → False) : F.card ≤ 3 := by
  apply (Finset.card_le_card (t := ((A ∪ B) ∪ C) \ ((A ∩ B) ∩ C)) ?_).trans
    (trigger_triangle A B C ha hb hc ab bc ca)
  intro p hp
  exact Finset.mem_sdiff.mpr ⟨readable hp, fun h => by
    simp only [Finset.mem_inter] at h
    exact cannot_fire_all p hp h.1.1 h.1.2 h.2⟩
end CrownCollision
