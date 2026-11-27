import Q1DoubleSplit
import DDPhysicalRows

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
open PEqualNP.CleanedNonEdge

def splitCuts (n : ℕ) (C : Circuit) (T : Finset ℕ) (m : ℕ) : Cuts where
  «omit» j := decide (j = m ∨ j ∈ T)
  bypass j b := decide (opnd C j b = n+m)

private theorem price_bound {n : ℕ} (s : Layout n) (r : Row) : price s r ≤ 1 := by
  unfold price
  split
  · decide
  · cases readPin s r.left <;> cases readPin s r.right <;> simp [andCost]

private theorem paid_plus_free {n : ℕ} (C : Circuit) (cuts : Cuts) (free : Finset ℕ)
    (isFree : ∀ i ∈ free, price (layout n C cuts i) (projectedRow n C cuts i) = 0)
    (k : ℕ) :
    expense (seed n) (rows n C cuts k) + ((Finset.range k).filter (· ∈ free)).card ≤ k := by
  induction k with
  | zero => simp [rows,expense]
  | succ k ih =>
    rw [expense_succ,Finset.range_add_one,Finset.filter_insert]
    by_cases hf : k ∈ free
    · simp [hf,isFree _ hf]; omega
    · have := price_bound (layout n C cuts k) (projectedRow n C cuts k)
      simp [hf]; omega

theorem split_budget {n : ℕ} (C : Circuit) (T : Finset ℕ) (m r : ℕ)
    (hT : T ⊆ Finset.range C.size) (hm : m < r) (hr : r < C.size)
    (hmT : m ∉ T) (hrT : r ∉ T)
    (pin : ∃ b : Fin 2, opnd C r b = n+m) :
    expense (seed n) (rows n C (splitCuts n C T m) C.size) + 2 + T.card ≤ C.size := by
  let p := splitCuts n C T m
  let S := insert m (insert r T)
  have skip (j : ℕ) (h : j = m ∨ j ∈ T) :
      price (layout n C p j) (projectedRow n C p j) = 0 := by
    simp [price,projectedRow,p,splitCuts,h]
  have free (j) (hj : j ∈ S) : price (layout n C p j) (projectedRow n C p j) = 0 := by
    rcases Finset.mem_insert.mp hj with eq | h
    · exact skip _ (Or.inl eq)
    rcases Finset.mem_insert.mp h with rfl | h
    · obtain ⟨b,hb⟩ := pin
      exact price_zero_of_bypass C p hm b (by simp [p,splitCuts,hb]) hb
    · exact skip _ (Or.inr h)
  have sub : S ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_range.mpr (hm.trans hr)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_range.mpr hr
    · exact hT hj
  have all : (Finset.range C.size).filter (· ∈ S) = S := by
    ext j
    exact ⟨fun hj => (Finset.mem_filter.mp hj).2, fun hj => Finset.mem_filter.mpr ⟨sub hj,hj⟩⟩
  have h := paid_plus_free C p S free C.size
  rw [all] at h
  have size : S.card = T.card+2 := by simp [S,hrT,hmT,hm.ne,Nat.add_assoc]
  rw [size] at h
  change expense (seed n) (rows n C p C.size) + 2 + T.card ≤ C.size
  omega

theorem split_from_slots {n : ℕ} (C : Circuit) (T : Finset ℕ) (m r : ℕ)
    (hT : T ⊆ Finset.range C.size) (hm : m < r) (hr : r < C.size)
    (hmT : m ∉ T) (hrT : r ∉ T) (pin : ∃ b : Fin 2, opnd C r b = n+m)
    (a b w : Signal n) (other : List (Signal n))
    (haveSlots : ∀ f ∈ a :: b :: w :: other, ∃ u,
      physicalSlot n C (splitCuts n C T m) C.size u = some f)
    (otherCount : other.length ≤ T.card)
    (sem : other.foldl (join false) (join true (join false a b) w) = circuitFun n C) :
    let k := expense (seed n) (rows n C (splitCuts n C T m) C.size)
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size+1 ∧
      wireVal n D (n+k) = join true a w ∧ wireVal n D (n+(k+1)) = join true b w ∧
      circuitFun n D = circuitFun n C := by
  dsimp only
  obtain ⟨B,tr,h⟩ := compiled_rows n C (splitCuts n C T m) C.size
  have banked (f) (hf : f ∈ a :: b :: w :: other) : B f := by
    obtain ⟨u,hu⟩ := haveSlots f hf
    have hu' := h u
    rw [hu] at hu'
    exact hu'
  have bound := split_budget C T m r hT hm hr hmT hrT pin
  exact split_competitor tr C a b w other (banked _ (by simp)) (banked _ (by simp))
    (banked _ (by simp)) (fun f hf => banked _ (by simp [hf])) (by omega) sem

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
