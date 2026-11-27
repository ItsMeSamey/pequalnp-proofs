import Q0FactorRows
import Q0Readers

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)

private noncomputable def prefixRows (k : ℕ) := (List.range k).map (rowOf G C g)
private noncomputable def state (k : ℕ) := (prefixRows G C g k).foldl next (seed n)

private theorem prefix_succ (k : ℕ) :
    prefixRows G C g (k+1) = prefixRows G C g k ++ [rowOf G C g k] := by
  simp [prefixRows, List.range_succ]

private theorem state_succ (k : ℕ) :
    state G C g (k+1) = next (state G C g k) (rowOf G C g k) := by
  simp [state, prefix_succ, List.foldl_append]

private theorem slot_snoc (s : Layout n) (r : Row) :
    ∃ v, (next s r).slots = s.slots ++ [v] := by
  rcases r with ⟨kind,l,r⟩
  cases kind <;> exact ⟨_, rfl⟩

private theorem state_length (k : ℕ) : (state G C g k).slots.length = n + k := by
  induction k with
  | zero => simp [state, prefixRows, seed]
  | succ k ih =>
    rw [state_succ]
    obtain ⟨v,h⟩ := slot_snoc (state G C g k) (rowOf G C g k)
    simp [h, ih, Nat.add_assoc]

private theorem source_pin (k : ℕ) (hk : g < k) :
    readPin (state G C g k) (n+g) = none := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [state_succ]
    by_cases eq : k = g
    · subst k
      change ((next (state G C g g) (rowOf G C g g)).slots).getD (n+g) none = none
      have h : (next (state G C g g) (rowOf G C g g)).slots =
          (state G C g g).slots ++ [none] := by simp [rowOf, next]
      rw [h, ← state_length G C g g]
      simp
    · have lt : g < k := by omega
      obtain ⟨v,h⟩ := slot_snoc (state G C g k) (rowOf G C g k)
      unfold readPin
      rw [h, List.getD_append _ _ _ _ (by rw [state_length]; omega)]
      exact ih lt

private theorem sources_next (s : Layout n) (r : Row) :
    (next s r).sources.length = s.sources.length + (if r.kind = .source then 1 else 0) := by
  rcases r with ⟨kind,l,r⟩
  cases kind <;> simp [next]

private theorem sources_prefix (k : ℕ) :
    (state G C g k).sources.length = if g < k then 1 else 0 := by
  induction k with
  | zero => simp [state, prefixRows, seed]
  | succ k ih =>
    rw [state_succ, sources_next, ih]
    by_cases eq : k = g
    · subst k; simp [rowOf]
    · have ns : (rowOf G C g k).kind ≠ .source := by
        simp only [rowOf, if_neg eq]
        split_ifs <;> decide
      rw [if_neg ns]
      by_cases h : g < k
      · simp [h, show g < k+1 by omega]
      · simp [h, show ¬ g < k+1 by omega]

theorem source_count (hlt : g < C.gates.length) : (doneLayout G C g).sources.length = 1 := by
  exact (sources_prefix G C g C.gates.length).trans (if_pos hlt)

private theorem expense_append (s : Layout n) (rs : List Row) (r : Row) :
    expense s (rs ++ [r]) = expense s rs + price (rs.foldl next s) r := by
  induction rs generalizing s with
  | nil => simp [expense]
  | cons t ts ih => simp [expense, ih, Nat.add_assoc]

private def counted (S : Finset ℕ) (k : ℕ) := ((Finset.range k).filter (· ∈ S)).card

private theorem counted_step (S : Finset ℕ) (k : ℕ) :
    counted S (k+1) = counted S k + (if k ∈ S then 1 else 0) := by
  classical
  by_cases hk : k ∈ S <;> simp [counted, Finset.range_add_one, Finset.filter_insert, hk]

private theorem counted_full {S : Finset ℕ} {k : ℕ} (h : S ⊆ Finset.range k) : counted S k = S.card := by
  unfold counted
  congr 1
  ext j
  exact ⟨fun hj => (Finset.mem_filter.mp hj).2, fun hj => Finset.mem_filter.mpr ⟨h hj,hj⟩⟩

private theorem price_le_one (s : Layout n) (r : Row) : price s r ≤ 1 := by
  unfold price
  split
  · decide
  · cases readPin s r.left <;> cases readPin s r.right <;> simp [andCost]

theorem row_savings {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hq : (orN G C \ lam G C).card = 0) {g : ℕ} (hg : g ∈ junk G C) :
    expense (seed n) (rowsOf G C g) + (readers n C g).card + (orT G C).card ≤ C.size := by
  let R := readers n C g
  let T := orT G C
  have hR : R ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have hT : T ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have bound (k : ℕ) :
      expense (seed n) (prefixRows G C g k) + counted R k + counted T k ≤ k := by
    induction k with
    | zero => simp [prefixRows, expense, counted]
    | succ k ih =>
      rw [prefix_succ, expense_append, counted_step, counted_step]
      change expense (seed n) (prefixRows G C g k) + price (state G C g k) (rowOf G C g k) +
        (counted R k + _) + (counted T k + _) ≤ k+1
      by_cases hr : k ∈ R
      · obtain ⟨hk, pin⟩ := Finset.mem_filter.mp hr
        have hlt := Finset.mem_range.mp hk
        have lt : g < k := by have := hAO.2.1 k hlt _ pin; omega
        have notOr := dirty_reader_not_or hAO hq hg hlt pin
        have ht : k ∉ T := fun h => notOr (Finset.mem_filter.mp h).2.1
        have zero : price (state G C g k) (rowOf G C g k) = 0 := by
          unfold price
          split
          · rfl
          · apply direct_cost
            rcases reader_pin hAO hlt pin with left | right
            · left; change readPin _ (opnd C k 0) = none
              rw [left]; exact source_pin G C g k lt
            · right; change readPin _ (opnd C k 1) = none
              rw [right]; exact source_pin G C g k lt
        simp only [if_pos hr, if_neg ht, zero]; omega
      · by_cases ht : k ∈ T
        · have hs : k ≠ g := by
            rintro rfl
            have ha := (Finset.mem_filter.mp hg).2.1
            have ho := (Finset.mem_filter.mp ht).2.1
            exact GateOp.noConfusion (ha.symm.trans ho)
          have kind : (rowOf G C g k).kind = .cleanOr := by simp [rowOf, hs, show k ∈ orT G C from ht]
          simp only [price, kind, if_true, if_neg hr, if_pos ht]
          omega
        · have := price_le_one (state G C g k) (rowOf G C g k)
          simp only [if_neg hr, if_neg ht]; omega
  have final := bound C.gates.length
  rw [counted_full hR, counted_full hT] at final
  exact final

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
