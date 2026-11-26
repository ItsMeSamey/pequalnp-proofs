import Research.SparseIncidence
import Research.IncidenceRobust

namespace IncidenceRobust
open SparseIncidence

variable {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

def mask (S : Finset (Vertex n)) : Input n :=
  (fun p => decide (Sum.inl p ∈ S), fun l => decide (Sum.inr l ∈ S))

private theorem sparse_mask (S : Finset (Vertex n)) :
    Fintype.card {l // (mask S).2 l = true} ≤ S.card := by
  let f : {l // (mask S).2 l = true} → S :=
    fun l => ⟨Sum.inr l.val,of_decide_eq_true l.property⟩
  have inj : Function.Injective f := fun a b h => Subtype.ext
    (Sum.inr.inj (congrArg Subtype.val h))
  simpa using Fintype.card_le_of_injective f inj

variable (out : Set (Input n)) (up : Upward out)
    (pos : ∀ p l, I p l → (single p,single l) ∈ out)
    (neg : ∀ b : Fin n → Bool, Fintype.card {l // b l = true} ≤ q →
      (outside I b,b) ∉ out)

include up pos neg in
theorem pair_test (hq : 2 ≤ q) (a c : Vertex n) :
    mask {a,c} ∈ out ↔ Edge I a c := by
  have small : ({a,c} : Finset _).card ≤ q := by
    have h := Finset.card_insert_le a ({c} : Finset _)
    simp only [Finset.card_singleton] at h
    omega
  rw [sparse_slice I out up pos neg _ _ (le_trans (sparse_mask _) small)]
  cases a <;> cases c <;> simp [mask,Edge]

include up pos neg in
theorem single_test (hq : 2 ≤ q) (a : Vertex n) :
    mask {a} ∉ out := by
  have h := pair_test I out up pos neg hq a a
  cases a <;> simpa [Edge] using h

variable (degree : ∀ l, Fintype.card {p // I p l} = q+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)

include degree unique up pos neg in
theorem essential_rows (hq : 2 ≤ q) (hn : n = q^2+q+1) (D : Finset (Vertex n))
    (small : D.card ≤ q) (a : Vertex n) (alive : a ∉ D) :
    ∃ c ∉ D, Disjoint ({a,c} : Finset _) D ∧
      mask {a,c} ∈ out ∧ mask {c} ∉ out := by
  obtain ⟨c,hc,e⟩ := has_neighbor I degree unique (by omega) hn D small a
  exact ⟨c,hc,by simp [alive,hc],(pair_test I out up pos neg hq a c).mpr e,
    single_test I out up pos neg hq c⟩

include degree unique up pos neg in
theorem transpose_rows (hq : 2 ≤ q) (hn : n = q^2+q+1) (D : Finset (Vertex n))
    (small : D.card < 2*q) {a b : Vertex n} (ab : a ≠ b) (ha : a ∉ D) (hb : b ∉ D) :
    ∃ c ∉ D, c ≠ a ∧ c ≠ b ∧
      Disjoint ({a,c} : Finset _) D ∧ Disjoint ({b,c} : Finset _) D ∧
      ((mask {a,c} ∈ out ∧ mask {b,c} ∉ out) ∨ (mask {b,c} ∈ out ∧ mask {a,c} ∉ out)) := by
  obtain ⟨c,hc,ca,cb,h⟩ := distinguish I degree unique (by omega) hn D small ab
  exact ⟨c,hc,ca,cb,by simp [ha,hc],by simp [hb,hc],by
    simpa only [pair_test I out up pos neg hq] using h⟩

end IncidenceRobust
