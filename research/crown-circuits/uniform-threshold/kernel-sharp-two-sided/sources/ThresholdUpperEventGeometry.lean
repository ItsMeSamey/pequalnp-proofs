import ThresholdUpperSecond
namespace ThresholdUpperEventGeometry
open ThresholdUpperSecond
open scoped BigOperators
theorem edge_two {w z} (u : Injection w z) (i : Fin w) : (u i).val.card=2 :=
  (Finset.mem_powersetCard.mp (u i).property).2
theorem terminal_le {w z} (u : Injection w z) (Q : Finset (Fin w)) :
    (terminal u Q).card≤2*Q.card := by
  simpa [terminal,edge_two,Nat.mul_comm] using
    (Finset.card_biUnion_le (s:=Q) (t:=fun i => (u i).val))

theorem tight {w z} (u : Injection w z) (Q : Finset (Fin w))
    (eq : (terminal u Q).card=2*Q.card) :
    (Q:Set (Fin w)).PairwiseDisjoint (fun i => (u i).val) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert i Q hi ih =>
    have cr := terminal_le u Q
    have un := Finset.card_union_add_card_inter (u i).val (terminal u Q)
    have ei := edge_two u i
    have tot : ((u i).val∪terminal u Q).card=2*(Q.card+1) := by
      simpa [terminal,hi,Finset.card_insert_of_notMem] using eq
    have inner : (terminal u Q).card=2*Q.card := by omega
    have zero : ((u i).val∩terminal u Q).card=0 := by omega
    have dis := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp zero)
    rw [Finset.coe_insert,Set.pairwiseDisjoint_insert_of_notMem hi]
    refine ⟨ih inner,?_⟩
    intro j hj
    exact dis.mono_right (fun a ha => Finset.mem_biUnion.mpr ⟨j,hj,ha⟩)

/-- Conditioned on the first Q, fresh images from R∖Q in a collision are
pairwise disjoint two-sets in a residual universe with exactly 2|R∖Q| sites. -/
theorem residual {w z} (u : Injection w z) (Q R : Finset (Fin w))
    (q4 : Q.card=4) (r4 : R.card=4)
    (q8 : (terminal u Q).card=8) (r8 : (terminal u R).card=8)
    (eq : terminal u R=terminal u Q) :
    let common := Q∩R
    let remaining := terminal u Q \ terminal u common
    remaining.card=2*(R \ Q).card ∧
      (∀ i∈R \ Q,(u i).val⊆remaining) ∧
      ((R \ Q : Finset (Fin w)):Set (Fin w)).PairwiseDisjoint (fun i => (u i).val) := by
  classical
  intro common remaining
  have qt := tight u Q (by omega)
  have rt := tight u R (by omega)
  have subset : terminal u common⊆terminal u Q := by
    intro a ha
    obtain ⟨i,hi,hit⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨i,(Finset.mem_inter.mp hi).1,hit⟩
  have cc : (terminal u common).card=2*common.card := by
    change (common.biUnion (fun i => (u i).val)).card=_
    have cd : (common:Set (Fin w)).PairwiseDisjoint (fun i => (u i).val) :=
      fun _ hi _ hj hn => qt (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hj).1 hn
    rw [Finset.card_biUnion cd]
    simp [edge_two,Nat.mul_comm]
  have diff := Finset.card_sdiff_add_card_inter R Q
  rw [Finset.inter_comm R Q] at diff
  change (R \ Q).card+common.card=R.card at diff
  refine ⟨?_,?_,fun _ hi _ hj hn => rt (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hn⟩
  · change (terminal u Q \ terminal u common).card=_
    rw [Finset.card_sdiff_of_subset subset,q8,cc]
    omega
  · intro i hi a hit
    obtain ⟨ir,iq⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_sdiff.mpr ⟨eq ▸ Finset.mem_biUnion.mpr ⟨i,ir,hit⟩,?_⟩
    intro shared
    obtain ⟨j,hj,ha⟩ := Finset.mem_biUnion.mp shared
    obtain ⟨jq,jr⟩ := Finset.mem_inter.mp hj
    exact Finset.disjoint_left.mp (rt ir jr (fun e => iq (e ▸ jq))) hit ha
end ThresholdUpperEventGeometry
