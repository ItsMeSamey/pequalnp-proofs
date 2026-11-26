import Research.CrownSixSilent

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem silent_incidence_strong {ρ γ : Type*} (R : Finset ρ) (G : Finset γ)
    (both : γ → Bool) (hit : ρ → γ → Bool)
    (neighbors : ∀ r ∈ R, 11 ≤ 8*(G.filter (fun g => hit r g && !both g)).card
      + (G.filter (fun g => hit r g && both g)).card)
    (capacity : ∀ g ∈ G, (R.filter (fun r => hit r g)).card ≤ if both g then 2 else 1) :
    4*R.card + (R.filter (fun r => 0 < (G.filter (fun g => hit r g && both g)).card)).card ≤ 2*G.card := by
  classical
  let charge (r : ρ) (g : γ) : ℕ :=
    2 * (if (hit r g && !both g) then 1 else 0) + (if (hit r g && both g) then 1 else 0)
  have row (r) (hr : r ∈ R) : (4 + if 0 < (G.filter (fun g => hit r g && both g)).card then 1 else 0) ≤ ∑ g ∈ G, charge r g := by
    simp only [charge,Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,Nat.cast_id]
    have h := neighbors r hr
    split <;> omega
  have col (g) (hg : g ∈ G) : ∑ r ∈ R, charge r g ≤ 2 := by
    have hc := capacity g hg
    simp only [charge,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,Nat.cast_id]
    cases h : both g <;> simp [h] at hc ⊢ <;> omega
  have lo := Finset.sum_le_sum row
  have hi := Finset.sum_le_sum col
  rw [Finset.sum_comm] at lo
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_boole,Nat.nsmul_eq_mul,Nat.cast_id] at lo hi
  change _ ≤ G.card * 2 at hi
  omega

def doubledSilent (C : Circuit) (R : Finset (Fin 24)) : Finset (Fin 24) :=
  R.filter (fun r => 0 < ((silentGates C R).filter (fun k => silentIncident C r k && silentBoth C R k)).card)

theorem silent_cross_doubled (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C) (R : Finset (Fin 24))
    (i j : Fin 12) (ne : i ≠ j) (ri : rowPort i ∈ R) (cj : colPort j ∈ R) :
    rowPort i ∈ doubledSilent C R ∧ colPort j ∈ doubledSilent C R := by
  obtain ⟨k,_,ok,rect⟩ := crown_first_charger C hm rep ne
  have cross : ((rowPort i ∈ rawSupport C (operand C k 0) ∧ colPort j ∈ rawSupport C (operand C k 1)) ∨
      (rowPort i ∈ rawSupport C (operand C k 1) ∧ colPort j ∈ rawSupport C (operand C k 0))) := by
    simpa only [chargingRect,Finset.mem_union,Finset.mem_product,rowSupport,colSupport,rawSupport,
      Finset.mem_filter,Finset.mem_univ,true_and] using rect
  have dh : silentBoth C R k = true := by
    apply decide_eq_true
    rcases cross with ⟨a,b⟩|⟨a,b⟩
    · exact ⟨⟨_,ri,a⟩,⟨_,cj,b⟩⟩
    · exact ⟨⟨_,cj,b⟩,⟨_,ri,a⟩⟩
  have mem (r) (hr : r ∈ R) (hit : silentIncident C r k = true) : r ∈ doubledSilent C R := by
    refine Finset.mem_filter.mpr ⟨hr,Finset.card_pos.mpr ⟨k,Finset.mem_filter.mpr ⟨?_,by simp [hit,dh]⟩⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok,r,hr,hit⟩
  constructor
  · apply mem _ ri (decide_eq_true ?_)
    rcases cross with ⟨a,_⟩|⟨a,_⟩
    · exact Or.inl a
    · exact Or.inr a
  · apply mem _ cj (decide_eq_true ?_)
    rcases cross with ⟨_,b⟩|⟨_,b⟩
    · exact Or.inr b
    · exact Or.inl b

private theorem six_dense_impossible (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : 24 ≤ (C.gates.filter isOrGate).length)
    (R : Finset (Fin 24)) (silent : ∀ r ∈ R, (trueOrFlags C.gates (singleInput r)).count true = 0)
    (six : R.card = 6)
    (inc : 2*R.card+2 ≤ ((avoidingAnds C ∅) \ (avoidingAnds C (silentCopyWires C R))).card) : False := by
  let S := Finset.univ \ R.image literalLabel
  let D := silentCopyWires C R
  have dead := induced_crown_and_lower C hm rep S D
    (fun i hi => silent_copies_avoid_intact C hm R silent i (Finset.mem_sdiff.mp hi).2)
  have intact : S.card = 12 - (R.image literalLabel).card := by
    dsimp only [S]; rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  have im := Finset.card_image_le (s := R) (f := literalLabel)
  have subset : avoidingAnds C D ⊆ avoidingAnds C ∅ := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Bool.and_eq_true_iff.mpr
      ⟨(Bool.and_eq_true_iff.mp (Finset.mem_filter.mp hk).2).1,List.all_eq_true.mpr (by simp)⟩⟩
  have difference := Finset.card_sdiff_of_subset subset
  have cap := all_and_count_balance C hm
  change 2*R.card+2 ≤ ((avoidingAnds C ∅) \ (avoidingAnds C D)).card at inc
  have kept := Finset.card_le_card subset
  have k : (avoidingAnds C D).card ≤ 2 := by omega
  have ub : 2 ^ (avoidingAnds C D).card ≤ 2^2 := Nat.pow_le_pow_right (by decide) k
  omega

theorem crown_six_silent_same_side (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length = 24)
    (R : Finset (Fin 24)) (six : R.card = 6)
    (sil : ∀ r ∈ R, (trueOrFlags C.gates (singleInput r)).count true = 0) :
    (∀ i : Fin 12, rowPort i ∉ R) ∨ (∀ j : Fin 12, colPort j ∉ R) := by
  classical
  by_contra! both
  obtain ⟨⟨i,ri⟩,j,cj⟩ := both
  have cover : R ⊆ doubledSilent C R ∪ {rowPort j,colPort i} := by
    intro r
    refine Fin.addCases (m:=12) (n:=12) (motive := fun r => r ∈ R → r ∈ doubledSilent C R ∪ {rowPort j,colPort i}) ?_ ?_ r
    · intro l hl
      by_cases same : l = j
      · subst l; simp [rowPort]
      · exact Finset.mem_union_left _ (silent_cross_doubled C hm rep R l j same hl cj).1
    · intro l hl
      by_cases same : i = l
      · subst l; simp [colPort]
      · exact Finset.mem_union_left _ (silent_cross_doubled C hm rep R i l same ri hl).2
  have count := Finset.card_le_card cover
  have unionCap := Finset.card_union_le (doubledSilent C R) {rowPort j,colPort i}
  have pairCap : ({rowPort j,colPort i} : Finset (Fin 24)).card ≤ 2 :=
    (Finset.card_insert_le ..).trans (by simp)
  have many : 4 ≤ (doubledSilent C R).card := by omega
  have weighted := silent_incidence_strong R (silentGates C R) (silentBoth C R) (silentIncident C)
    (silent_physical_row C hm rep ors.le R sil)
    (silent_column_capacity C R (fun r hr => rawSupport_eq_singleton C hm r (sil r hr)))
  change 4*R.card + (doubledSilent C R).card ≤ _ at weighted
  have inc := Finset.card_le_card (silent_gate_deleted C R)
  have d : 2*R.card+2 ≤ ((avoidingAnds C ∅) \ (avoidingAnds C (silentCopyWires C R))).card := by omega
  exact six_dense_impossible C hm rep size ors.ge R sil six d

end PEqualNP.Research.MissingCell
