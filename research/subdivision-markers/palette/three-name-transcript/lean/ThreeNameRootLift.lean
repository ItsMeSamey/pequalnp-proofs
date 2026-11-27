import ThreeNameSplitCircuit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

namespace ThreeNameRootLift
open ThreeNameSplitCircuit
open scoped BigOperators
variable {ι V : Type*} [DecidableEq ι] [AddCommGroup V]

/-- Shrink a zero sum that uses all roots. Every zero subset must use either
all roots or none; the latter kind can be removed without changing the sum. -/
theorem extract (v : ι → V) (R U : Finset ι) (rn : R.Nonempty)
    (ru : R ⊆ U) (uz : (∑ i ∈ U, v i) = 0)
    (mixed : ∀ D ⊆ U, (∑ i ∈ D, v i) = 0 → R ⊆ D ∨ Disjoint R D) :
    ∃ C ⊆ U, R ⊆ C ∧ Circuit v C := by
  classical
  induction U using Finset.strongInductionOn
  rename_i U ih
  by_cases sub : ∃ D ⊂ U, R ⊆ D ∧ (∑ i ∈ D, v i) = 0
  · obtain ⟨D,hD,hR,hz⟩ := sub
    obtain ⟨C,hC,hr,hc⟩ := ih D hD hR hz (fun T ht => mixed T (ht.trans hD.le))
    exact ⟨C,hC.trans hD.le,hr,hc⟩
  · refine ⟨U,fun _ hi => hi,ru,rn.mono ru,uz,?_⟩
    intro D hu hn hz
    by_contra ne
    rcases mixed D hu hz with rd | dj
    · exact sub ⟨D,lt_of_le_of_ne hu ne,rd,hz⟩
    · have hr : R ⊆ U \ D := fun i hi => Finset.mem_sdiff.mpr ⟨ru hi,Finset.disjoint_left.mp dj hi⟩
      have sum := Finset.sum_sdiff (f := v) hu
      rw [hz,add_zero,uz] at sum
      exact sub ⟨U \ D,Finset.sdiff_ssubset hu hn,hr,sum⟩


/-- For independent named columns, the exact-line root trace leaves only
the empty root subset and the full root subset in a zero dependence. -/
theorem lift (v : ι → V) (R U : Finset ι) (rn : R.Nonempty)
    (ru : R ⊆ U) (uz : (∑ i ∈ U, v i) = 0) (indep : Independent v R)
    (trace : ∀ D ⊆ U, (∑ i ∈ D, v i) = 0 →
      (∑ i ∈ R ∩ D, v i) = 0 ∨ (∑ i ∈ R ∩ D, v i) = ∑ i ∈ R, v i) :
    ∃ C ⊆ U, R ⊆ C ∧ Circuit v C := by
  classical
  apply extract v R U rn ru uz
  intro D hu hz
  have hsub : R ∩ D ⊆ R := Finset.inter_subset_left
  rcases trace D hu hz with h | h
  · right
    apply Finset.disjoint_left.mpr
    intro i hi hd
    exact indep _ hsub ⟨i,Finset.mem_inter.mpr ⟨hi,hd⟩⟩ h
  · left
    have sum := Finset.sum_sdiff (f := v) hsub
    rw [h] at sum
    have z : (∑ i ∈ R \ (R ∩ D), v i) = 0 := add_right_cancel (sum.trans (zero_add _).symm)
    intro i hi
    by_contra hd
    have hm : i ∈ R \ (R ∩ D) := Finset.mem_sdiff.mpr ⟨hi,fun hmem => hd (Finset.mem_inter.mp hmem).2⟩
    exact indep _ Finset.sdiff_subset ⟨i,hm⟩ z

/-- Ordinary sum witness S and the exact trace of its ordinary span imply
a circuit containing all named labels. No circuit-oracle hypothesis. -/
theorem from_trace (v : ι → V) (R S : Finset ι) (rn : R.Nonempty)
    (dj : Disjoint R S) (binary : ∀ x : V, x + x = 0)
    (indep : Independent v R) (target : (∑ i ∈ S, v i) = ∑ i ∈ R, v i)
    (trace : ∀ Q ⊆ S, ∀ P ⊆ R, (∑ i ∈ Q, v i) = (∑ i ∈ P, v i) →
      (∑ i ∈ P, v i) = 0 ∨ (∑ i ∈ P, v i) = ∑ i ∈ R, v i) :
    ∃ C ⊆ R ∪ S, R ⊆ C ∧ Circuit v C := by
  classical
  have hz : (∑ i ∈ R ∪ S, v i) = 0 := by rw [Finset.sum_union dj,target,binary]
  apply lift v R (R ∪ S) rn Finset.subset_union_left hz indep
  · intro D hD hZ
    let P := R ∩ D
    let Q := D \ P
    have hp : P ⊆ D := Finset.inter_subset_right
    have hq : Q ⊆ S := by
      intro i hi
      have hd := Finset.mem_sdiff.mp hi
      rcases Finset.mem_union.mp (hD hd.1) with hr | hs
      · exact False.elim (hd.2 (Finset.mem_inter.mpr ⟨hr,hd.1⟩))
      · exact hs
    have sum : (∑ i ∈ Q, v i) + (∑ i ∈ P, v i) = 0 :=
      (Finset.sum_sdiff (f := v) hp).trans hZ
    exact trace Q hq P Finset.inter_subset_left (add_right_cancel (sum.trans (binary _).symm))

#print axioms from_trace
#print axioms lift
#print axioms extract
end ThreeNameRootLift
