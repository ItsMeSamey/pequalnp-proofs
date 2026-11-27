import DDMultiCut
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor

private theorem factorPriceBound {n : ℕ} (s : Layout n) (r : Row) : price s r ≤ 1 := by
  unfold price
  split
  · decide
  · cases readPin s r.left <;> cases readPin s r.right <;> simp [andCost]

private theorem factorPaidFree {n : ℕ} (C : Circuit) (cuts : Cuts) (free : Finset ℕ)
    (isFree : ∀ i ∈ free, price (layout n C cuts i) (projectedRow n C cuts i) = 0)
    (k : ℕ) :
    expense (seed n) (rows n C cuts k) + ((Finset.range k).filter (· ∈ free)).card ≤ k := by
  induction k with
  | zero => simp [rows,expense]
  | succ k ih =>
    rw [expense_succ,Finset.range_add_one,Finset.filter_insert]
    by_cases hf : k ∈ free
    · simp [hf,isFree _ hf]; omega
    · have := factorPriceBound (layout n C cuts k) (projectedRow n C cuts k)
      simp [hf]; omega

theorem multi_cut_cost {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (sources : Finset ℕ) :
    expense (seed n) (rows n C (multiCuts n C sources) C.size) +
      (sources.biUnion (readers n C)).card ≤ C.size := by
  classical
  let R := sources.biUnion (readers n C)
  have free {j} (hj : j ∈ R) :
      price (layout n C (multiCuts n C sources) j) (projectedRow n C (multiCuts n C sources) j) = 0 := by
    obtain ⟨s,hs,hr⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hj',pin⟩ := Finset.mem_filter.mp hr
    have len := Finset.mem_range.mp hj'
    have back := ao.2.1 j len _ pin
    obtain ⟨b,hb⟩ : ∃ b : Fin 2, opnd C j b = n+s := by
      rcases Q0.reader_pin ao len pin with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
    exact price_zero_of_bypass C _ (by omega : s<j) b (by simp [multiCuts,hb,hs]) hb
  have sub : R ⊆ Finset.range C.size := by
    intro j hj
    obtain ⟨s,_,hr⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hr).1
  have all : (Finset.range C.size).filter (· ∈ R) = R := by
    ext i
    exact ⟨fun hi => (Finset.mem_filter.mp hi).2, fun hi => Finset.mem_filter.mpr ⟨sub hi,hi⟩⟩
  have bound := factorPaidFree C (multiCuts n C sources) R (fun _ hj => free hj) C.size
  rwa [all] at bound

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
