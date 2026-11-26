import Research.SharedLocalSlots
import Research.IncidenceRobust
import Mathlib.Data.Fintype.EquivFin

namespace PlaneSharedSlots
open SharedLocalSlots

theorem example_formula {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l) (hq : 0 < q) (hn : n=q^2+q+1) :
    ∃ f : ℕ → ℕ → ℕ,
      (∀ x y : ℕ → Prop, eval x y (top f n q) ↔
        ∃ p l : Fin n, I p l ∧ x p.val ∧ y l.val) ∧
      (∀ p : Fin n, ∀ l : ℕ, (∃ j ≤ q, f p.val j = l) ↔
        ∃ k : Fin n, I p k ∧ k.val=l) ∧
      (∀ p : Fin n, row_local_list f q p.val (top f n q) = merges f n q) ∧
      (merges f n q).length = q := by
  classical
  let S (p : Fin n) := IncidenceRobust.lines I p
  have size (p : Fin n) : Fintype.card (S p) = q+1 := by
    simpa [S] using IncidenceRobust.lines_card I degree unique hq hn p
  let e (p : Fin n) := Fintype.equivFinOfCardEq (size p)
  let f (p j : ℕ) := if hp : p < n then
    if hj : j < q+1 then (((e ⟨p,hp⟩).symm ⟨j,hj⟩).val).val else 0 else 0
  have entry (p : Fin n) (j : Fin (q+1)) : f p.val j.val = ((e p).symm j).val.val := by
    simp [f,p.isLt,j.isLt]
  have valid (p : Fin n) (j : Fin (q+1)) : I p ((e p).symm j).val := by
    exact (Finset.mem_filter.mp ((e p).symm j).property).2
  have equiv (p : Fin n) (l : ℕ) : (∃ j ≤ q, f p.val j=l) ↔ ∃ k : Fin n, I p k ∧ k.val=l := by
    constructor
    · rintro ⟨j,hj,h⟩
      let z : Fin (q+1) := ⟨j,by omega⟩
      exact ⟨((e p).symm z).val, valid p z,(entry p z).symm.trans h⟩
    · rintro ⟨k,hk,rfl⟩
      let t : S p := ⟨k,by simpa [S,IncidenceRobust.lines] using hk⟩
      let z := e p t
      exact ⟨z.val,by have := z.isLt; omega,(entry p z).trans (by simp [z,t])⟩
  refine ⟨f,?_,equiv,?_,merge_count _ _ _⟩
  · intro x y
    rw [top_eval]
    constructor
    · rintro ⟨j,hj,p,hp,hx,hy⟩
      let z : Fin n := ⟨p,hp⟩
      obtain ⟨k,hk,e⟩ := (equiv z _).mp ⟨j,hj,rfl⟩
      exact ⟨z,k,hk,hx,e ▸ hy⟩
    · rintro ⟨p,k,hk,hx,hy⟩
      obtain ⟨j,hj,e⟩ := (equiv p k.val).mpr ⟨k,hk,rfl⟩
      exact ⟨j,hj,p.val,p.isLt,hx,e ▸ hy⟩
  · intro p
    apply all_local_coincide f n q q p.val p.isLt le_rfl
    let a : Fin (q+1) := ⟨0,by omega⟩
    let b : Fin (q+1) := ⟨1,by omega⟩
    intro same
    have h : ((e p).symm a).val.val = ((e p).symm b).val.val :=
      (entry p a).symm.trans (same.trans (entry p b))
    have ab := (e p).symm.injective (Subtype.ext (Fin.ext h))
    exact Nat.zero_ne_one (congrArg Fin.val ab)

end PlaneSharedSlots
