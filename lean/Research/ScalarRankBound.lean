import Research.ScalarLocalGates
import Research.RectangleRowReuse
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace ScalarRankBound
open SparseIncidence SparseQueryCut ScalarLocalGates IncidenceRobust

/-- The membership matrix on singleton point and line inputs is a union of r rectangles. -/
def RankLE {n : ℕ} (X : ℕ → Set (Input n)) (g r : ℕ) :=
  ∃ R C : Fin r → Finset (Fin n), ∀ p l : Fin n,
    (single p,single l) ∈ X (n+n+g) ↔ ∃ i, p ∈ R i ∧ l ∈ C i

private theorem count {n s c h : ℕ} (K : Fin n → ℕ → Finset (Fin n)) (A : Fin n → Finset (Fin n))
    (H : Finset ℕ) (few : H.card ≤ h)
    (good : ∀ g < s, g ∉ H →
      (Finset.univ.filter (fun p : Fin n => 2 ≤ (K p g).card ∧ K p g ⊆ A p)).card ≤ c) :
    (∑ p : Fin n, ((Finset.range s).filter (fun g => 2 ≤ (K p g).card ∧ K p g ⊆ A p)).card)
      ≤ n*h+s*c := by
  classical
  let use (g : ℕ) := Finset.univ.filter (fun p : Fin n => 2 ≤ (K p g).card ∧ K p g ⊆ A p)
  have per (g : ℕ) (hg : g ∈ Finset.range s) : (use g).card ≤ (if g ∈ H then n else 0)+c := by
    by_cases hit : g ∈ H
    · have b := Finset.card_le_card (Finset.filter_subset (s:=Finset.univ) (p:=fun p : Fin n => 2 ≤ (K p g).card ∧ K p g ⊆ A p))
      simp only [Finset.card_univ,Fintype.card_fin] at b
      simpa [use,hit] using (Nat.le_trans b (Nat.le_add_right n (c)))
    · simpa [use,hit] using good g (Finset.mem_range.mp hg) hit
  have cap : ((Finset.range s).filter (fun g => g∈H)).card ≤ h :=
    le_trans (Finset.card_le_card (fun _ hg => (Finset.mem_filter.mp hg).2)) few
  have rearrange : (∑ p : Fin n, ((Finset.range s).filter (fun g => 2 ≤ (K p g).card ∧ K p g ⊆ A p)).card) =
      ∑ g ∈ Finset.range s, (use g).card := by
    simp only [use,Finset.card_filter]
    rw [Finset.sum_comm]
  rw [rearrange]
  calc
    _ ≤ ∑ g ∈ Finset.range s, ((if g ∈ H then n else 0)+c) := Finset.sum_le_sum per
    _ = ((Finset.range s).filter (fun g => g∈H)).card*n + s*c := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp
    _ ≤ _ := by
      rw [Nat.mul_comm n h]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ cap) _

theorem lower : (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∀ (r h : ℕ) (H : Finset ℕ), H.card ≤ h →
      (∀ g < x9, g ∉ H → RankLE x12 g r) →
      x2*x1 ≤ x2*h+x9*((r+1).choose 2) ∧ x2*x1 ≤ x2*h+x9*r^2) := by
  classical
  intro q n I inst hq hn degree unique s o tags X ho inputs tagged pos neg margin r h H few ranks
  let K := fun (p : Fin n) (g : ℕ) => profile (wires X p) (n+n+g)
  let A := lines I
  have total := ScalarLocalGates.total q n I hq hn degree unique s o tags X ho inputs tagged pos neg margin
  have forGate (g : ℕ) (hg : g<s) (ok : g∉H) :
      (Finset.univ.filter (fun p : Fin n => 2 ≤ (K p g).card ∧ K p g ⊆ A p)).card ≤ (r+1).choose 2 ∧
      (Finset.univ.filter (fun p : Fin n => 2 ≤ (K p g).card ∧ K p g ⊆ A p)).card ≤ r^2 := by
    obtain ⟨R,C,cover⟩ := ranks g hg ok
    have exactness (p l : Fin n) : l ∈ K p g ↔ ∃ i, p∈R i ∧ l∈C i := by
      change l ∈ profile _ _ ↔ _
      rw [mem_profile]
      change row p {l} ∈ X _ ↔ _
      have e : row p {l} = (single p,single l) := by
        apply Prod.ext
        · rfl
        · funext k; simp [row,single]
      rw [e]
      exact cover p l
    have overlap := fun (p t : Fin n) (ne : p ≠ t) => line_overlap I unique ne
    exact ⟨RectangleRowReuse.card_rows_choose A (fun p => K p g) r R C overlap exactness,
      RectangleRowReuse.card_rows A (fun p => K p g) r R C overlap exactness⟩
  constructor
  · exact le_trans total (count K A H few (fun g hg ok => (forGate g hg ok).1))
  · exact le_trans total (count K A H few (fun g hg ok => (forGate g hg ok).2))

end ScalarRankBound
