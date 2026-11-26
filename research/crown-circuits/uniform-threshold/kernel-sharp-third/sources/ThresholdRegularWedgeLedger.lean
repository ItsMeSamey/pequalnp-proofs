import ThresholdSelectedLosses
import ThresholdNativeGraphMoments
namespace ThresholdNativeRowSelection
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSharedPartition ThresholdHighComponents
open ThresholdEffectiveColumns ThresholdSecondaryReceivers ThresholdWarmSimple ThresholdPurityPins
open ThresholdFanoutBudget ThresholdFlowSum ThresholdSharedFlow ThresholdNativeColumnCharge
open ThresholdAmbientEffectiveGraph ThresholdNativeGraphMoments ThresholdCodegreeRecords
open scoped BigOperators

private theorem two_budgets {w g A D holes coarse actual degreeSum : Nat}
    (c : actual≤coarse) (f : actual≤holes+2*degreeSum)
    (adj : A^2≤g*(A+D+6*actual))
    (non : 2*D^2≤(w*(w-1)-2*g)*(4*actual+D)) (deg : degreeSum=2*(A+D)+2*g) :
    A^2≤g*(A+D+6*coarse) ∧ 2*D^2≤w^2*(4*coarse+D) ∧
    2*D^2≤w^2*(4*(holes+4*(A+D)+4*g)+D) := by
  have m : w*(w-1)-2*g≤w^2 := by
    have le := Nat.mul_le_mul_left w (Nat.sub_le w 1)
    simp only [pow_two]; omega
  exact ⟨adj.trans (Nat.mul_le_mul_left _ (by omega)),non.trans (Nat.mul_le_mul m (by omega)),
    non.trans (Nat.mul_le_mul m (by omega))⟩

set_option maxHeartbeats 2000000 in
theorem generic_moments {I X : Type*} [Fintype X] [decX : DecidableEq X] [decI : DecidableEq I]
    (R : Finset I) (col : I→Finset X) (two : ∀ r∈R,(col r).card=2)
    (inj : Set.InjOn col (R:Set I)) :
    let W := support R col
    let G := activeGraph R col
    let A := ∑ p∈edges G,(neighbors G p).card
    let D := ∑ p∈nonedges G,(neighbors G p).card
    let f := ∑ F : Four W,((ThresholdEffectiveMatchingRows.fiber R col (ambientBox W F)).card-1)
    A^2≤R.card*(A+D+6*f) ∧ 2*D^2≤(W.card*(W.card-1)-2*R.card)*(4*f+D) ∧
    (∑ v,G.degree v^2)=2*(A+D)+2*R.card ∧ (2*R.card)^2≤W.card*(2*(A+D)+2*R.card) := by
  classical
  intro T H A D loss
  let dec : DecidableRel H.Adj := inferInstanceAs (DecidableRel (activeGraph R col).Adj)
  letI : DecidableRel H.Adj := dec
  let chart := fun F : Four T =>
    (Fintype.equivFinOfCardEq (by simpa using F.property : Fintype.card ↥F.val=4)).symm
  have valid : R.image col⊆T.powersetCard 2 := by
    intro q hit
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hit
    exact Finset.mem_powersetCard.mpr ⟨fun _ hv => Finset.mem_biUnion.mpr ⟨r,hr,hv⟩,two r hr⟩
  have g : H.edgeFinset.card=R.card := (ThresholdFamilySimpleGraph.edge_card T (R.image col) valid).trans (Finset.card_image_of_injOn inj)
  have w : Fintype.card ↥T=T.card := Fintype.card_coe _
  have box (F : Four T) :=
    @ThresholdEffectiveMatchingRows.box_graph I X decI decX R col T two inj
      ((chart F).toEmbedding.trans (Function.Embedding.subtype (·∈F.val))) dec
  have lossEq : (∑ F, (ThresholdFourSetOccupancy.occupancy (ThresholdFourSetOccupancy.ofGraph H (chart F 0).val (chart F 1).val
    (chart F 2).val (chart F 3).val)-1))=loss := by
    apply Finset.sum_congr rfl
    intro F _
    have lift (i : Fin 4) :
        ((chart F).toEmbedding.trans (Function.Embedding.subtype (·∈F.val))) i = (chart F i).val := rfl
    have k := (box F).symm
    rw [chart_box, lift, lift, lift, lift] at k
    apply congrArg (fun c : Nat => c-1)
    exact k
  rw [←g,←w,←lossEq]
  exact @ThresholdNativeGraphMoments.moments (↥T) _ _ H dec chart

set_option maxHeartbeats 120000 in
theorem wedge_bounds {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (R : Finset (Id (source gs out))) (sub : R⊆retained (layout n gs out minim.eligible))
    (two : ∀ r∈R,(effective (layout n gs out minim.eligible) minim r).card=2)
    (inj : Set.InjOn (effective (layout n gs out minim.eligible) minim) (R:Set _)) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let col := effective L minim
    let W := support R col
    let G := activeGraph R col
    let w := W.card
    let g := R.card
    let holes := (inner L H).card
    let coarse := holes+2*H.card*((hubs C n) \ H).card
    ∃ A D : Nat,
      A^2≤g*(A+D+6*coarse) ∧
      2*D^2≤w^2*(4*coarse+D) ∧
      2*D^2≤w^2*(4*(holes+4*(A+D)+4*g)+D) ∧
      (∑ v,G.degree v^2)=2*(A+D)+2*g ∧
      (2*g)^2≤w*(2*(A+D)+2*g) := by
  classical
  intro C L H col W G w g holes coarse
  let A := ∑ p∈edges G,(neighbors G p).card
  let D := ∑ p∈nonedges G,(neighbors G p).card
  let loss := ∑ F : Four W,((ThresholdEffectiveMatchingRows.fiber R col (ambientBox W F)).card-1)
  obtain ⟨c,f⟩ := both_losses hn minim reg R sub two inj
  change loss≤coarse at c
  change loss≤holes+2*∑ v,G.degree v^2 at f
  have m := generic_moments R col two inj
  change A^2≤g*(A+D+6*loss) ∧ 2*D^2≤(w*(w-1)-2*g)*(4*loss+D) ∧
    (∑ v,G.degree v^2)=2*(A+D)+2*g ∧ (2*g)^2≤w*(2*(A+D)+2*g) at m
  obtain ⟨adj,non,degree,wedge⟩ := m
  obtain ⟨a,b,k⟩ := two_budgets c f adj non degree
  exact ⟨A,D,a,b,k,degree,wedge⟩
end ThresholdNativeRowSelection
