import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

namespace ThresholdColumnPeel
variable {I V : Type*} [DecidableEq I] [DecidableEq V]
variable (onCol : V → I → Prop) [∀ v r, Decidable (onCol v r)]

def hits (R : Finset I) (v : V) := R.filter (onCol v)

def Supported (R : Finset I) (S : Finset V) : Prop :=
  ∀ r∈R, ∀ v, onCol v r → v∈S

def MinTwo (R : Finset I) : Prop :=
  ∀ r∈R, ∀ v, onCol v r → ∃ b∈R, b≠r ∧ onCol v b

/-- Repeatedly delete a column with at most one active row. The same row
identity survives in every subsequent subfamily. Charge at most one lost
row per removed column, including isolated columns. -/
theorem peel (S : Finset V) (R : Finset I) (sup : Supported onCol R S) :
    ∃ T⊆S, ∃ K⊆R, Supported onCol K T ∧ MinTwo onCol K ∧
      R.card+T.card≤K.card+S.card := by
  classical
  induction S using Finset.strongInductionOn generalizing R
  rename_i S ih
  by_cases bad : ∃ v∈S, (hits onCol R v).card≤1
  · obtain ⟨v,hv,h1⟩ := bad
    let D := hits onCol R v
    let R' := R \ D
    have sub : D⊆R := Finset.filter_subset _ _
    have subR : R'⊆R := Finset.sdiff_subset
    have newSup : Supported onCol R' (S.erase v) := by
      intro r hr u hu
      obtain ⟨old,no⟩ := Finset.mem_sdiff.mp hr
      apply Finset.mem_erase.mpr
      refine ⟨?_,sup r old u hu⟩
      rintro rfl
      exact no (Finset.mem_filter.mpr ⟨old,hu⟩)
    obtain ⟨T,tS,K,kR,good,two,cost⟩ :=
      ih _ (Finset.erase_ssubset hv) R' newSup
    refine ⟨T,tS.trans (Finset.erase_subset _ _),K,kR.trans subR,good,two,?_⟩
    have eqR : R'.card=R.card-D.card := Finset.card_sdiff_of_subset sub
    have eqS := Finset.card_erase_of_mem hv
    have spos : 0<S.card := Finset.card_pos.mpr ⟨v,hv⟩
    have dR := Finset.card_le_card sub
    change D.card≤1 at h1
    omega
  · refine ⟨S,Finset.Subset.rfl,R,Finset.Subset.rfl,sup,?_,le_rfl⟩
    intro r hr v hv
    have many : 1<(hits onCol R v).card := by
      by_contra! small
      exact bad ⟨v,sup r hr v hv,small⟩
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp many
    obtain ⟨ar,av⟩ := Finset.mem_filter.mp ha
    obtain ⟨br,bv⟩ := Finset.mem_filter.mp hb
    by_cases e : a=r
    · exact ⟨b,br,fun f => ab (e.trans f.symm),bv⟩
    · exact ⟨a,ar,e,av⟩

/-- Rows failing the uniform pivot threshold cost at most total incidences
divided by that threshold. This statement also permits missing pivots. -/
theorem bad_cost (R : Finset I) (errors : I → Nat) (b : Nat) :
    b*(R.filter (fun r => b≤errors r)).card≤∑ r∈R,errors r := by
  classical
  let B := R.filter (fun r => b≤errors r)
  calc
    _ = ∑ _r∈B, b := by simp [B,Nat.mul_comm]
    _ ≤ ∑ r∈B, errors r := Finset.sum_le_sum (fun r hr => (Finset.mem_filter.mp hr).2)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Finite two-pass ledger. Original low-degree witnesses remain available in
K, while effective witnesses are drawn from G after the hot-row deletion. -/
theorem two_stage {W : Type*} [DecidableEq W]
    (eff : W → I → Prop) [∀ w r, Decidable (eff w r)]
    (S : Finset V) (T : Finset W) (R privateRows badRows : Finset I)
    (origSup : Supported onCol (R \ privateRows) S)
    (effSup : Supported eff (R \ privateRows) T) :
    ∃ K⊆R \ privateRows, ∃ G⊆K \ badRows, MinTwo onCol K ∧ MinTwo eff G ∧
      R.card≤G.card+privateRows.card+badRows.card+S.card+T.card := by
  classical
  obtain ⟨_,_,K,hK,_,mk,ck⟩ := peel onCol S _ origSup
  have sup : Supported eff (K \ badRows) T :=
    fun r hr => effSup r (hK (Finset.mem_sdiff.mp hr).1)
  obtain ⟨_,_,G,hG,_,mg,cg⟩ := peel eff T _ sup
  refine ⟨K,hK,G,hG,mk,mg,?_⟩
  have loss (a b : Finset I) : a.card≤(a \ b).card+b.card := by
    have cover : a⊆(a \ b)∪b := by
      intro i hi
      by_cases inside : i∈b
      · exact Finset.mem_union_right _ inside
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,inside⟩)
    exact (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have one := loss R privateRows
  have two := loss K badRows
  omega
end ThresholdColumnPeel
