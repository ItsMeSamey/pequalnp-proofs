import Research.CrownCircuitLabels
namespace PEqualNP.Research.MissingCell.CrownLabels
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

theorem classify {n} (U V : Finset (Fin n)) (cap : (U ∪ V).card ≤ 2) :
    U = ∅ ∨ V = ∅ ∨ Common U V ∨ Early U V ∨ Early V U ∨ Disjoint U V := by
  classical
  by_cases a : U = ∅
  · exact Or.inl a
  by_cases b : V = ∅
  · exact Or.inr (Or.inl b)
  refine Or.inr (Or.inr ?_)
  have u := Finset.nonempty_iff_ne_empty.mpr a
  have v := Finset.nonempty_iff_ne_empty.mpr b
  by_cases d : Disjoint U V
  · exact Or.inr (Or.inr (Or.inr d))
  have inter := Finset.not_disjoint_iff_nonempty_inter.mp d
  rcases lt_trichotomy (U.min' u) (V.min' v) with l|e|r
  · exact Or.inr (Or.inl ⟨_,_,l,CrownLabelCap.N_shape U V _ _ (U.min'_mem u) (V.min'_mem v) l
      (V.min'_le) inter cap⟩)
  · exact Or.inl ⟨u,v,e⟩
  · exact Or.inr (Or.inr (Or.inl ⟨_,_,r,CrownLabelCap.N_shape V U _ _ (V.min'_mem v)
      (U.min'_mem u) r U.min'_le (Finset.inter_comm U V ▸ inter) (Finset.union_comm U V ▸ cap)⟩))

open scoped Classical in
private noncomputable def adjusted {n} (U V : Finset (Fin n)) (bad : Bool) : ℕ :=
  if bad = false ∧ Early U V then 2 else CrownLabelCap.weight U.card

private theorem at_least (k : ℕ) (cap : k ≤ 2) : 1 ≤ CrownLabelCap.weight k := by
  interval_cases k <;> decide

theorem early_cards {n} (X Y : Finset (Fin n)) (e : Early X Y) : X.card = 2 ∧ Y.card = 1 := by
  rcases e with ⟨g,h,lt,rfl,rfl⟩
  simp [ne_of_lt lt]

open scoped Classical in
private theorem local_point {n} (U V : Finset (Fin n)) (bad : Bool) (cap : (U ∪ V).card ≤ 2) :
    (if Common U V then 0 else 2) + (if U = ∅ ∨ V = ∅ then 1 else 0) ≤
      (adjusted U V bad - 1) + (adjusted V U bad - 1) + (if bad then 1 else 0) := by
  classical
  have a := (Finset.card_le_card (Finset.subset_union_left : U ⊆ U ∪ V)).trans cap
  have b := (Finset.card_le_card (Finset.subset_union_right : V ⊆ U ∪ V)).trans cap
  have loU := at_least U.card a
  have loV := at_least V.card b
  have emp (X Y : Finset (Fin n)) (e : X = ∅ ∨ Y = ∅) : ¬ Early X Y := by
    intro h
    obtain ⟨h1,h2⟩ := early_cards X Y h
    rcases e with eq|eq <;> simp_all
  have step (X Y : Finset (Fin n)) (hn : Early X Y) :
      2 ≤ (adjusted X Y bad - 1) + (adjusted Y X bad - 1) + (if bad then 1 else 0) := by
    obtain ⟨wx,wy⟩ := early_cards X Y hn
    have rev : ¬Early Y X := by intro e; have := early_cards Y X e; omega
    cases bad <;> simp [adjusted,hn,rev,wx,wy,CrownLabelCap.weight]
  by_cases empty : U = ∅ ∨ V = ∅
  · have er := emp U V empty
    have ec := emp V U empty.symm
    have large : 5 ≤ CrownLabelCap.weight U.card + CrownLabelCap.weight V.card := by
      rcases empty with rfl|rfl
      · rw [Finset.card_empty, show CrownLabelCap.weight 0 = 4 by decide]; omega
      · rw [Finset.card_empty, show CrownLabelCap.weight 0 = 4 by decide]; omega
    simp only [adjusted,er,ec,and_false,ite_false,ite_eq_left empty]
    split_ifs <;> omega
  · simp only [ite_eq_right empty, Nat.add_zero]
    by_cases sh : Common U V
    · simp [sh]
    simp only [ite_eq_right sh]
    rcases classify U V cap with e|e|e|e|e|d
    · exact (empty (Or.inl e)).elim
    · exact (empty (Or.inr e)).elim
    · exact (sh e).elim
    · exact step U V e
    · simpa only [Nat.add_comm (adjusted V U bad - 1) (adjusted U V bad - 1)] using step V U e
    · have neU : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun e => empty (Or.inl e))
      have neV : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun e => empty (Or.inr e))
      rw [Finset.card_union_of_disjoint d] at cap
      have hU := Finset.card_pos.mpr neU
      have hV := Finset.card_pos.mpr neV
      have u1 : U.card = 1 := by omega
      have v1 : V.card = 1 := by omega
      have e1 : ¬ Early U V := by intro h; have := early_cards U V h; omega
      have e2 : ¬ Early V U := by intro h; have := early_cards V U h; omega
      cases bad <;> simp [adjusted,e1,e2,u1,v1,CrownLabelCap.weight]

theorem pointwise (C : Circuit) (bad : Finset L) (i : L) (hc : (A C i ∪ B C i).card ≤ 2) :
    (if i ∈ shared C then 0 else 2) + (if i ∈ silent C then 1 else 0) ≤
    (adjustedQuarter C bad (rowPort i) - 1) + (adjustedQuarter C bad (colPort i) - 1) +
      (if i ∈ bad then 1 else 0) := by
  classical
  have p := local_point (A C i) (B C i) (decide (i ∈ bad)) hc
  simp only [adjustedQuarter,row_clean,col_clean,qsig]
  simpa [shared,silent,adjusted,A,B] using p

theorem adjusted_pos (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (bad : Finset L) (t : Fin 24) :
    1 ≤ adjustedQuarter C bad t := by
  have h := singletonQuarter_cases C t (literal_count_le_two C hm rep ors t)
  unfold adjustedQuarter
  split <;> omega

theorem mem_shared (C : Circuit) (i : L) :
    i ∈ shared C ↔ Common (A C i) (B C i) := by
  classical simp only [shared,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def strongShared (C : Circuit) : Finset L :=
  (shared C).filter fun i => (A C i).card = 2 ∧ (B C i).card = 2
noncomputable def weakShared (C : Circuit) : Finset L := shared C \ strongShared C
def disjointLabels (C : Circuit) : Finset L := Finset.univ.filter fun i =>
  (A C i).Nonempty ∧ (B C i).Nonempty ∧ Disjoint (A C i) (B C i)

theorem total_excess (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (bad : Finset L)
    (few : (shared C).card ≤ 5) (paid : bad.card ≤ (silent C).card) :
    14 ≤ ∑ i : L, ((adjustedQuarter C bad (rowPort i) - 1) + (adjustedQuarter C bad (colPort i) - 1)) :=
  CrownDemandArithmetic.aggregate_excess _ _ _ _ _ few paid
    (fun i => pointwise C bad i (union_cap C hm rep ors i))

end PEqualNP.Research.MissingCell.CrownLabels
