import ThresholdNativeRowSelection
namespace ThresholdNativeRowSelection
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSharedPartition
open ThresholdSecondaryReceivers ThresholdHighComponents ThresholdEffectiveColumns ThresholdPurityPins
open ThresholdSharedFlow ThresholdFlowSum ThresholdFanoutBudget ThresholdWarmSimple ThresholdHubMissing
open scoped BigOperators
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def trimCost :=
  2*ThresholdHubMissing.M L+(retained L).card+2*(high L).card*((hubs C n) \ high L).card

theorem floor_trim (T a b m c : Nat) (total : T=m+c)
    (A : (T.sqrt+1)*a≤m) (B : (T.sqrt+1)*b≤c) : a+b≤T.sqrt := by
  have cap := Nat.add_le_add A B
  rw [←Nat.mul_add,←total] at cap
  by_contra! bad
  have lo := Nat.mul_le_mul_left (T.sqrt+1) bad
  have hi := Nat.lt_succ_sqrt T
  nlinarith

/-- Complete two-core witnesses under the single native floor-square-root
threshold, with uniform upper bounds for each final row's bad pivot sets. -/
theorem regular_selected {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (space : let L := layout n gs out minim.eligible
      9*trimCost L < (high L).card^2) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let u := (trimCost L).sqrt
    let O := receivers C n H
    ∃ K⊆retained L, ∃ G⊆K,
      ThresholdColumnPeel.MinTwo (fun v r => v∈signature C n r) K ∧
      ThresholdColumnPeel.MinTwo (fun v r => v∈effective L minim r) G ∧
      (∀ a∈G,(effective L minim a).card=2) ∧ Set.InjOn (effective L minim) (G : Set _) ∧
      (∀ a∈G,a∈good C n H ∧ (makeBlock L Fin.val a).exts=[] ∧
        (missing L H a).card≤u ∧ (exceptional L minim H a).card≤u) ∧
      H.card≤G.card+(impure L H).card+deltaO L+2*(andIds C).length+
        (allPrivate L).card+u+2*O.card := by
  classical
  intro C L H u O
  let R := retained L
  let BM := R.filter (fun r=>u+1≤(missing L H r).card)
  let R1 := R \ BM
  let BC := R1.filter (fun r=>u+1≤(exceptional L minim H r).card)
  have usq : u*u≤trimCost L := Nat.sqrt_le _
  have room : 2*u+u<H.card := by
    by_contra! bad
    have low := Nat.mul_le_mul bad bad
    change 9*trimCost L<H.card^2 at space
    nlinarith
  obtain ⟨K,kR,G,gK,orig,eff,card,inj,miss,cold,price⟩ := regular_ledger hn minim reg u u room
  have bs : BM.card+BC.card≤u := floor_trim _ _ _ _ _ rfl miss cold
  have oo : (O.image (column L minim)).card≤O.card := Finset.card_image_le
  have kg : G⊆K := gK.trans Finset.sdiff_subset
  have kr : K⊆R := kR.trans Finset.sdiff_subset
  refine ⟨K,kr,G,kg,orig,eff,card,inj,?_,?_⟩
  · intro a ag
    have ak := kg ag
    have a1 := kR ak
    obtain ⟨ar,noM⟩ := Finset.mem_sdiff.mp a1
    have noC := (Finset.mem_sdiff.mp (gK ag)).2
    have gp := good_pure L (Finset.mem_sdiff.mp ar).1
    refine ⟨gp.1,gp.2,?_,?_⟩
    · by_contra! bad; exact noM (Finset.mem_filter.mpr ⟨ar,bad⟩)
    · by_contra! bad; exact noC (Finset.mem_filter.mpr ⟨a1,bad⟩)
  · change H.card≤G.card+(impure L H).card+deltaO L+2*(andIds C).length+
      (allPrivate L).card+BM.card+BC.card+O.card+(O.image (column L minim)).card at price
    omega
end ThresholdNativeRowSelection
