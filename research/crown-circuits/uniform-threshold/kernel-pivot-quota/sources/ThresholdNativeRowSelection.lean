import ThresholdWarmAveraging
import ThresholdWarmRetention
import ThresholdPurityPins
import ThresholdGoodCount
import ThresholdPhysicalReceiverGraph
namespace ThresholdNativeRowSelection
open scoped BigOperators
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSharedPartition
open ThresholdSecondaryReceivers ThresholdHighComponents ThresholdEffectiveColumns ThresholdPurityPins
open ThresholdSharedFlow ThresholdFlowSum ThresholdFanoutBudget ThresholdWarmSimple
variable {C : Circuit} {n : Nat} (L : Layout C n)

noncomputable def pureGood := good C n (high L) \ impure L (high L)
noncomputable def allPrivate := (pureGood L).filter (fun r =>
  Disjoint (signature C n r) (hubs C n))
noncomputable def retained := pureGood L \ allPrivate L

theorem purity_count : (high L).card ≤ (pureGood L).card+
    (impure L (high L)).card+deltaO L+2*(andIds C).length := by
  classical
  have keep := Finset.card_sdiff_add_card_inter (good C n (high L)) (impure L (high L))
  have cnt := Finset.card_le_card (Finset.inter_subset_right :
    good C n (high L)∩impure L (high L) ⊆impure L (high L))
  have base := good_count L (high L) (Finset.filter_subset _ _)
  dsimp [pureGood]
  omega

theorem good_pure {r : Id C} (hr : r∈pureGood L) :
    r∈good C n (high L) ∧ (makeBlock L Fin.val r).exts=[] := by
  have h := Finset.mem_sdiff.mp hr
  refine ⟨h.1,?_⟩
  by_contra bad
  exact h.2 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h.1).1,bad⟩)

theorem miss_total (two : ∀ x,(endpoints L x).card=2) (inj : Function.Injective (endpoints L))
    (R : Finset (Id C)) (sub : R⊆high L) :
    (∑ r∈R,(ThresholdWarmSimple.missing L (high L) r).card) ≤ 2*ThresholdHubMissing.M L+R.card := by
  classical
  let A := (Finset.univ : Finset (Fin n)).image (endpoints L)
  let Q := ThresholdC4Missing.missing (high L) A
  have cap : Q.card≤ThresholdHubMissing.M L := ThresholdPhysicalReceiverGraph.missing_global L two inj _ (Finset.filter_subset _ _)
  have tally := ThresholdWarmAveraging.missing_total R (ThresholdWarmSimple.missing L (high L)) Q
    (fun e he => (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2) (by
      intro r hr F hf ne
      obtain ⟨inH,abs⟩ := Finset.mem_filter.mp hf
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨?_,by simp [ne.symm]⟩,?_⟩
      · intro x hx; rcases Finset.mem_insert.mp hx with rfl|z
        · exact sub hr
        · obtain rfl := Finset.mem_singleton.mp z; exact inH
      · intro h
        obtain ⟨x,_,eq⟩ := Finset.mem_image.mp h
        exact abs ⟨ne,x,eq.trans (Finset.pair_comm _ _)⟩)
  omega

private theorem has_shared (r : Id C) (hr : r∈retained L) :
    ∃ S∈signature C n r,S∈hubs C n := by
  classical
  obtain ⟨keep,abs⟩ := Finset.mem_sdiff.mp hr
  by_contra! none
  apply abs
  exact Finset.mem_filter.mpr ⟨keep,Finset.disjoint_left.mpr none⟩

private theorem marked_hub (S : Id C) (sH : S∈hubs C n) : boundary (n:=n) S := by
  apply Or.inr
  have share := (List.mem_filter.mp (List.mem_toFinset.mp sH)).1
  simpa using (List.mem_filter.mp share).2

/-- All cold incidences are counted on the fixed pool before either deletion
by missing-degree threshold or deletion by cold-degree threshold. -/
theorem cold_before_deletion {n out : Nat} {gs : List ResidualSurplus.Raw}
    (hn : 2≤n) (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    let H := high L
    let R := retained L
    (∑ r∈R,(exceptional L M H r).card)≤2*H.card*((hubs C n) \ H).card := by
  classical
  intro C L H R
  have subH : H⊆hubs C n := Finset.filter_subset _ _
  have goodR (r) (hr : r∈R) := (good_pure L (Finset.mem_sdiff.mp hr).1).1
  have pureR (r) (hr : r∈R) := (good_pure L (Finset.mem_sdiff.mp hr).1).2
  refine ThresholdWarmAveraging.native_cold hn M reg R H ((hubs C n) \ H) ?_ goodR pureR ?_
  · exact Finset.disjoint_left.mpr (fun _ a b => (Finset.mem_sdiff.mp b).2 a)
  · dsimp only
    intro r hr F bad
    obtain ⟨S,sr,sH⟩ := has_shared L r hr
    have g := goodR r hr
    have rH := (Finset.mem_filter.mp g).1
    have early := receiver_later L g sr
    have outside : S∉H := by
      intro hi
      exact ThresholdPhysicalIdeals.high_antichain M reg r rH S hi
        ((ThresholdPhysicalIdeals.mem_pair L r S).mpr ⟨⟨subH rH,sH⟩,early.1.ne,early.2⟩)
    have fh := (Finset.mem_filter.mp bad).1
    have fs : F≠S := fun eq => outside (eq ▸ fh)
    have two := signature_two L (regular_inputs n gs out M.eligible reg).1 M hn H subH r g
    obtain ⟨p,q,ne,eq⟩ := Finset.card_eq_two.mp two
    have other : ∃ P,P≠S ∧ signature C n r={S,P} := by
      rw [eq] at sr
      rcases Finset.mem_insert.mp sr with s|s
      · subst S; exact ⟨q,ne.symm,eq⟩
      · obtain rfl := Finset.mem_singleton.mp s
        exact ⟨p,ne,eq.trans (Finset.pair_comm _ _)⟩
    obtain ⟨P,pS,sig⟩ := other
    have fa : F≠r := by
      rintro rfl
      obtain ⟨_,x,xe,_⟩ := Finset.mem_filter.mp bad
      have sz := (classified_simple hn M reg).1 x
      simp [xe] at sz
    exact ⟨S,Finset.mem_sdiff.mpr ⟨sH,outside⟩,to_cold M H R F S r P hr fa
      (marked_hub S sH) sig pS bad⟩

theorem regular_ledger {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) (mu e : Nat)
    (room : 2*mu+e<(high (layout n gs out minim.eligible)).card) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let R := retained L
    let O := receivers C n H
    let T := O.image (column L minim)
    let BM := R.filter (fun r => mu+1≤(missing L H r).card)
    let R1 := R \ BM
    let BC := R1.filter (fun r => e+1≤(exceptional L minim H r).card)
    ∃ K⊆R1, ∃ G⊆K \ BC,
      ThresholdColumnPeel.MinTwo (fun v r => v∈signature C n r) K ∧
      ThresholdColumnPeel.MinTwo (fun v r => v∈effective L minim r) G ∧
      (∀ a∈G,(effective L minim a).card=2) ∧ Set.InjOn (effective L minim) (G : Set _) ∧
      (mu+1)*BM.card≤2*ThresholdHubMissing.M L+R.card ∧
      (e+1)*BC.card≤2*H.card*((hubs C n) \ H).card ∧
      H.card≤G.card+(impure L H).card+deltaO L+2*(andIds C).length+
        (allPrivate L).card+BM.card+BC.card+O.card+T.card := by
  classical
  intro C L H R O T BM R1 BC
  have hh : H⊆hubs C n := Finset.filter_subset _ _
  have gr (r) (hr : r∈R) := (good_pure L (Finset.mem_sdiff.mp hr).1).1
  have subR : R1⊆R := Finset.sdiff_subset
  have mis (r) (hr : r∈R1) : (missing L H r).card≤mu := by
    have h := Finset.mem_sdiff.mp hr
    by_contra! bad
    exact h.2 (Finset.mem_filter.mpr ⟨h.1,bad⟩)
  have support (r) (hr : r∈R1) (v) (hv : v∈signature C n r) : v∈O :=
    Finset.mem_biUnion.mpr ⟨r,gr r (subR hr),hv⟩
  have old : ThresholdColumnPeel.Supported (fun v r=>v∈signature C n r) (R1 \ ∅) O :=
    fun r hr v hv => support r (Finset.mem_sdiff.mp hr).1 v hv
  have newS : ThresholdColumnPeel.Supported (fun v r=>v∈effective L minim r) (R1 \ ∅) T := by
    intro r hr v hv
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨s,support r (Finset.mem_sdiff.mp hr).1 s hs,rfl⟩
  obtain ⟨K,k0,G,g0,oc,fc,sz,inj,loss,bc⟩ := two_cores (by omega) minim reg H R1 ∅ O T hh
    (fun r hr=>gr r (subR hr)) old newS (fun r hr=>by
      obtain ⟨v,vr,vh⟩ := has_shared L r (subR (Finset.mem_sdiff.mp hr).1)
      exact ⟨v,vr,marked_hub v vh⟩) mu e room (fun r hr=>mis r (Finset.mem_sdiff.mp hr).1)
  have simple := classified_simple (by omega) minim reg
  have totalM := miss_total L simple.1 simple.2.1 R (fun r hr=>(Finset.mem_filter.mp (gr r hr)).1)
  have bm := (ThresholdColumnPeel.bad_cost R (fun r=>(missing L H r).card) (mu+1)).trans totalM
  have totalC := cold_before_deletion (by omega) minim reg
  have cmp : (∑ r∈R1,(exceptional L minim H r).card)≤∑ r∈R,(exceptional L minim H r).card :=
    Finset.sum_le_sum_of_subset subR
  have warm := bc.trans (cmp.trans totalC)
  have c1 := Finset.card_sdiff_add_card_eq_card (show BM⊆R from Finset.filter_subset _ _)
  have c2 := Finset.card_sdiff_add_card_eq_card (show allPrivate L⊆pureGood L from Finset.filter_subset _ _)
  have c3 := purity_count L
  change R1.card+BM.card=R.card at c1
  change R.card+(allPrivate L).card=(pureGood L).card at c2
  change H.card≤(pureGood L).card+(impure L H).card+deltaO L+2*(andIds C).length at c3
  simp only [Finset.card_empty,Nat.add_zero] at loss
  change R1.card≤G.card+BC.card+O.card+T.card at loss
  exact ⟨K,by simpa using k0,G,g0,oc,fc,sz,inj,bm,warm,by omega⟩
end ThresholdNativeRowSelection
