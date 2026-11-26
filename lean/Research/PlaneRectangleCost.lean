import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Fin.Basic

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PlaneRectangleCost

abbrev Vertex := Fin 13

def D : Finset Vertex := {0, 1, 3, 9}
def edges : Finset (Vertex × Vertex) := Finset.univ.filter fun p => p.1 - p.2 ∈ D

private theorem edgeCount : edges.card = 52 := by decide +kernel
private theorem commonSize : ∀ a b : Vertex, a ≠ b →
    (Finset.univ.filter fun j => a-j ∈ D ∧ b-j ∈ D).card ≤ 1 := by decide +kernel

private theorem noSquare (a b c d : Vertex) (ab : a ≠ b) (cd : c ≠ d)
    (ac : a-c ∈ D) (ad : a-d ∈ D) (bc : b-c ∈ D) (bd : b-d ∈ D) : False := by
  apply cd
  exact Finset.card_le_one.mp (commonSize a b ab) c (by simp [ac,bc]) d (by simp [ad,bd])

private theorem rowSize : ∀ a : Vertex, (Finset.univ.filter fun b => a-b ∈ D).card = 4 := by decide +kernel
private theorem colSize : ∀ b : Vertex, (Finset.univ.filter fun a => a-b ∈ D).card = 4 := by decide +kernel

/-- A nonempty legal rectangle is a star of size at most four. -/
private theorem star (A B : Finset Vertex) (ha : A.Nonempty) (hb : B.Nonempty)
    (safe : ∀ a ∈ A, ∀ b ∈ B, a-b ∈ D) :
    (A.card = 1 ∨ B.card = 1) ∧ A.card ≤ 4 ∧ B.card ≤ 4 := by
  obtain ⟨a,ha'⟩ := ha
  obtain ⟨b,hb'⟩ := hb
  have ac : A ⊆ Finset.univ.filter (fun i => i-b ∈ D) := by
    intro i hi; simp [safe i hi b hb']
  have bc : B ⊆ Finset.univ.filter (fun j => a-j ∈ D) := by
    intro j hj; simp [safe a ha' j hj]
  refine ⟨?_, (Finset.card_le_card ac).trans (colSize b).le,
    (Finset.card_le_card bc).trans (rowSize a).le⟩
  by_contra! h
  obtain ⟨i,hi,j,hj,ij⟩ := (Finset.one_lt_card (s := A)).mp (by have := Finset.card_pos.mpr ⟨a,ha'⟩; omega)
  obtain ⟨k,hk,l,hl,kl⟩ := (Finset.one_lt_card (s := B)).mp (by have := Finset.card_pos.mpr ⟨b,hb'⟩; omega)
  exact noSquare i j k l ij kl (safe i hi k hk) (safe i hi l hl) (safe j hj k hk) (safe j hj l hl)

/-- Each term builds its two nonempty ORs and one AND; the final OR uses m-1 gates. -/
theorem cost (m : ℕ) (A B : Fin m → Finset Vertex)
    (ha : ∀ i, (A i).Nonempty) (hb : ∀ i, (B i).Nonempty)
    (exactCover : Finset.univ.biUnion (fun i => (A i) ×ˢ (B i)) = edges) :
    64 ≤ (∑ i, (((A i).card - 1) + ((B i).card - 1) + 1)) + (m-1) := by
  have shape (i : Fin m) := star (A i) (B i) (ha i) (hb i) (by
    intro a ha' b hb'
    have h : (a,b) ∈ edges := exactCover ▸ Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨ha', hb'⟩⟩
    exact (Finset.mem_filter.mp h).2)
  let size := fun i : Fin m => (A i).card * (B i).card
  have eqcost (i : Fin m) : ((A i).card-1) + ((B i).card-1) + 1 = size i := by
    dsimp [size]
    have pa := Finset.card_pos.mpr (ha i)
    have pb := Finset.card_pos.mpr (hb i)
    rcases (shape i).1 with h|h <;> simp [h] <;> omega
  have small (i : Fin m) : size i ≤ 4 := by
    dsimp [size]
    obtain ⟨h,aa,bb⟩ := shape i
    rcases h with h|h <;> simp [h,aa,bb]
  have total : 52 ≤ ∑ i, size i := by
    rw [← edgeCount, ← exactCover]
    simpa [size] using Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m)))
      (t := fun i => (A i) ×ˢ (B i))
  have upper : (∑ i, size i) ≤ m*4 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => small i)
  simp_rw [eqcost]
  omega

end PlaneRectangleCost
