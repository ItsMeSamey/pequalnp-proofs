import IncidenceStartNormalization
import Research.IncidenceRobust
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace IncidenceLineGateBooking
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceRobust
open scoped BigOperators
variable {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

noncomputable def support (C : Circuit n) (g : Fin C.size) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => (single p,fun _=>false) ∈ C.wire (n+n+g.val))
def avoid (x w : Fin n) : Fin n → Bool := fun p => decide (¬I p x ∧ ¬I p w)

theorem wire_mono (C : Circuit n) (g : Fin C.size) : Upward (C.wire (n+n+g.val)) := by
  apply wire_upward C.wire C.inputs (g:=C.size) _ _ (by omega)
  intro j hj
  let t := C.code j
  obtain ⟨ha,hb⟩ := C.earlier j hj
  refine ⟨t.left,ha,t.right,hb,?_⟩
  have h := C.law j hj
  change C.wire (n+n+j)=t.eval C.wire at h
  cases ht : t.op with
  | join => exact Or.inl (by simpa [Gate.eval,ht,Op.eval] using h)
  | copy => exact Or.inr (Or.inl (by simpa [Gate.eval,ht,Op.eval] using h))
  | zero => exact Or.inr (Or.inr (Or.inl (by simpa [Gate.eval,ht,Op.eval] using h)))
  | meet => exact Or.inr (Or.inr (Or.inr (by simpa [Gate.eval,ht,Op.eval] using h)))

theorem support_covered (C : Circuit n) (g : Fin C.size) (x w : Fin n)
    (cold : (avoid I x w,fun _=>false) ∉ C.wire (n+n+g.val)) :
    support C g ⊆ points I x ∪ points I w := by
  classical
  intro p hp
  by_contra missing
  have inc : ¬I p x ∧ ¬I p w := by simpa [points] using missing
  apply cold
  apply wire_mono C g (u:=(single p,fun _=>false)) _ (by simpa [support] using hp)
  refine ⟨?_,fun _ h => h⟩
  intro i hi
  have e : i=p := of_decide_eq_true hi
  subst i
  simpa [avoid] using inc

theorem heavy_owner (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (S : Finset (Fin n)) (x w y : Fin n) (cover : S⊆points I x ∪ points I w)
    (heavy : 2 < (points I y ∩ S).card) : y=x ∨ y=w := by
  by_contra miss
  push_neg at miss
  have sub : points I y ∩ S ⊆ (points I y ∩ points I x) ∪ (points I y ∩ points I w) := by
    intro p hp
    obtain ⟨hy,hs⟩ := Finset.mem_inter.mp hp
    rcases Finset.mem_union.mp (cover hs) with h|h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hy,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hy,h⟩)
  have h := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have h1 := point_overlap I unique miss.1
  have h2 := point_overlap I unique miss.2
  omega

theorem gate_single_owner (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (C : Circuit n) (charged : Finset (Fin n)) (wit : Fin n→Fin n)
    (book : Fin n→Finset (Fin C.size × Fin n))
    (cold : ∀ x∈charged, ∀ z∈book x, (avoid I x (wit x),fun _=>false) ∉ C.wire (n+n+z.1.val))
    (heavy : ∀ x∈charged, ∀ z∈book x, 2<(points I x ∩ support C z.1).card)
    (unpaired : ∀ x∈charged, ∀ y∈charged, x≠y → wit x=y → wit y≠x) :
    ∀ x∈charged, ∀ y∈charged, ∀ u∈book x, ∀ v∈book y, u.1=v.1 → x=y := by
  intro x hx y hy u hu v hv eq
  by_contra ne
  have ca := support_covered I C u.1 _ _ (cold x hx u hu)
  have cb := support_covered I C v.1 _ _ (cold y hy v hv)
  have A := heavy_owner I unique _ x (wit x) y ca (by rw [eq]; exact heavy y hy v hv)
  have B := heavy_owner I unique _ y (wit y) x cb (by rw [←eq]; exact heavy x hx u hu)
  exact unpaired x hx y hy ne (A.resolve_left (Ne.symm ne)).symm (B.resolve_left ne).symm

theorem booked_disjoint (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (C : Circuit n) (charged : Finset (Fin n)) (wit : Fin n→Fin n)
    (book : Fin n→Finset (Fin C.size × Fin n))
    (cold : ∀ x∈charged, ∀ z∈book x, (avoid I x (wit x),fun _=>false) ∉ C.wire (n+n+z.1.val))
    (heavy : ∀ x∈charged, ∀ z∈book x, 2<(points I x ∩ support C z.1).card)
    (unpaired : ∀ x∈charged, ∀ y∈charged, x≠y → wit x=y → wit y≠x) :
    (charged : Set (Fin n)).PairwiseDisjoint book := by
  intro x hx y hy ne
  apply Finset.disjoint_left.mpr
  intro z zx zy
  exact ne (gate_single_owner I unique C charged wit book cold heavy unpaired x hx y hy z zx z zy rfl)

theorem actual_pair_bound (C : Circuit n) (charged : Finset (Fin n))
    (book : Fin n→Finset (Fin C.size × Fin n))
    (h : (charged : Set (Fin n)).PairwiseDisjoint book)
    (many : ∀ x∈charged, 3106≤(book x).card) :
    3106*charged.card≤(charged.biUnion book).card := by
  rw [Finset.card_biUnion h]
  calc
    3106 * charged.card = ∑ _x ∈ charged, 3106 := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum many

#print axioms booked_disjoint
end IncidenceLineGateBooking
