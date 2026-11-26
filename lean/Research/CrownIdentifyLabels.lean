import Research.CrownIdentifyCore

namespace PEqualNP.Research.CrownIdentify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

noncomputable def rawPairIds : (gs : List Gate) → ℕ → Finset (Fin gs.length) := by
  classical
  exact fun gs n =>
    match gs with
    | [] => ∅
    | g::rest =>
      let tail := (rawPairIds rest (n+1)).map (Fin.succEmb _)
      if isRawPair g n then insert 0 tail else tail

theorem rawPairIds_card (gs : List Gate) (n : ℕ) : (rawPairIds gs n).card = pairCount gs n := by
  classical
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    have h0 : (0 : Fin (gs.length+1)) ∉ (rawPairIds gs (n+1)).map (Fin.succEmb _) := by simp
    by_cases h : isRawPair g n <;> simp [rawPairIds,pairCount,h,h0,ih,Nat.add_comm]

theorem rawPairIds_mem (gs : List Gate) (n : ℕ) (k : Fin gs.length) :
    k ∈ rawPairIds gs n ↔ ∃ i : Fin 12, readAt gs n k.val = {i.val,12+i.val} := by
  classical
  induction gs generalizing n with
  | nil => exact Fin.elim0 k
  | cons g gs ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · change (0 : Fin (gs.length+1)) ∈ rawPairIds (g::gs) n ↔ isRawPair g n
      by_cases h : isRawPair g n <;> simp [rawPairIds,h]
    · by_cases h : isRawPair g n <;> simp [rawPairIds,h,readAt,ih]

/-- Distinct labels cannot charge the same physical gate: its unique raw
input below 12 identifies the label. -/
theorem labels_le_pairCount (C : Circuit) (L : Finset (Fin 12))
    (occurs : ∀ i ∈ L, ∃ k : Fin C.gates.length, readAt C.gates 24 k.val = {i.val,12+i.val}) :
    L.card ≤ pairCount C.gates 24 := by
  classical
  let k (i : L) := (occurs i.val i.property).choose
  have eq (i : L) : readAt C.gates 24 (k i).val = {i.val.val,12+i.val.val} :=
    (occurs i.val i.property).choose_spec
  let lift (i : L) : rawPairIds C.gates 24 :=
    ⟨k i,(rawPairIds_mem ..).mpr ⟨i.val,eq i⟩⟩
  have inj : Function.Injective lift := by
    intro i j he
    have ke : k i = k j := congrArg Subtype.val he
    have both := (eq i).symm.trans ((congrArg (fun g : Fin C.gates.length => readAt C.gates 24 g.val) ke).trans (eq j))
    have mem : i.val.val ∈ ({j.val.val,12+j.val.val} : Finset ℕ) := both ▸ Finset.mem_insert_self ..
    apply Subtype.ext
    apply Fin.ext
    rcases Finset.mem_insert.mp mem with h | h
    · exact h
    · have := Finset.mem_singleton.mp h
      omega
  simpa [rawPairIds_card] using Fintype.card_le_of_injective lift inj

end PEqualNP.Research.CrownIdentify
