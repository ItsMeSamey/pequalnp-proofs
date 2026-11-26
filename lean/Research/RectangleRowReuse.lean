import Mathlib.Data.Sym.Card

namespace RectangleRowReuse

variable {P V : Type*} [Fintype P] [DecidableEq V]
open scoped Sym2

theorem card_rows_choose (A K : P → Finset V) (r : ℕ) (R : Fin r → Finset P) (C : Fin r → Finset V)
    (overlap : ∀ p t : P, p ≠ t → (A p ∩ A t).card ≤ 1)
    (exactness : ∀ p v, v ∈ K p ↔ ∃ i, p ∈ R i ∧ v ∈ C i) :
    (Finset.univ.filter (fun p => 2 ≤ (K p).card ∧ K p ⊆ A p)).card ≤ (r+1).choose 2 := by
  classical
  let L := Finset.univ.filter (fun p => 2 ≤ (K p).card ∧ K p ⊆ A p)
  have spec (p : L) := (Finset.mem_filter.mp p.property).2
  have pair (p : L) : ∃ z : Sym2 (Fin r), (∀ i ∈ z, p.val ∈ R i) ∧
      ∃ v ∈ K p.val, ∃ w ∈ K p.val, v ≠ w ∧ (∃ i ∈ z, v ∈ C i) ∧ (∃ i ∈ z, w ∈ C i) := by
    obtain ⟨v,hv,w,hw,ne⟩ := Finset.one_lt_card.mp (spec p).1
    obtain ⟨i,ri,ci⟩ := (exactness _ _).mp hv
    obtain ⟨j,rj,cj⟩ := (exactness _ _).mp hw
    refine ⟨s(i,j),?_,v,hv,w,hw,ne,⟨i,Sym2.mem_iff.mpr (Or.inl rfl),ci⟩,
      ⟨j,Sym2.mem_iff.mpr (Or.inr rfl),cj⟩⟩
    intro k hk
    rcases Sym2.mem_iff.mp hk with rfl|rfl
    · exact ri
    · exact rj
  let code (p : L) := (pair p).choose
  have inj : Function.Injective code := by
    intro p t eq
    by_contra ne
    have distinct : p.val ≠ t.val := fun h => ne (Subtype.ext h)
    obtain ⟨_,v,hv,w,hw,vw,⟨i,hi,hci⟩,⟨j,hj,hcj⟩⟩ := (pair p).choose_spec
    have cover := (pair t).choose_spec.1
    change ∀ i ∈ code t, t.val ∈ R i at cover
    change i ∈ code p at hi
    change j ∈ code p at hj
    have vt := (exactness t.val v).mpr ⟨i,cover i (eq ▸ hi),hci⟩
    have wt := (exactness t.val w).mpr ⟨j,cover j (eq ▸ hj),hcj⟩
    exact vw (Finset.card_le_one.mp (overlap _ _ distinct) v
      (Finset.mem_inter.mpr ⟨(spec p).2 hv,(spec t).2 vt⟩) w
      (Finset.mem_inter.mpr ⟨(spec p).2 hw,(spec t).2 wt⟩))
  have count := Fintype.card_le_of_injective code inj
  change Fintype.card L ≤ Fintype.card (Sym2 (Fin r)) at count
  rw [Fintype.card_coe,Sym2.card,Fintype.card_fin] at count
  exact count

theorem card_rows (A K : P → Finset V) (r : ℕ) (R : Fin r → Finset P) (C : Fin r → Finset V)
    (overlap : ∀ p t : P, p ≠ t → (A p ∩ A t).card ≤ 1)
    (exactness : ∀ p v, v ∈ K p ↔ ∃ i, p ∈ R i ∧ v ∈ C i) :
    (Finset.univ.filter (fun p => 2 ≤ (K p).card ∧ K p ⊆ A p)).card ≤ r^2 := by
  apply le_trans (card_rows_choose A K r R C overlap exactness)
  cases r with
  | zero => decide
  | succ r =>
    rw [Nat.choose_two_right,Nat.add_sub_cancel]
    have h := Nat.mul_le_mul_right (r+1) (show r+1+1 ≤ (r+1)+(r+1) by omega)
    have rhs : ((r+1)+(r+1))*(r+1) = (r+1)^2+(r+1)^2 := by rw [Nat.add_mul,Nat.pow_two]
    rw [rhs] at h
    omega

end RectangleRowReuse
