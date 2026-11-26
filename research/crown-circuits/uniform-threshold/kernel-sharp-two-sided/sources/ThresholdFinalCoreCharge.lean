import ThresholdNativeColumnCharge
import ThresholdNativeSharpCoreRows
namespace ThresholdFinalCoreCharge
open PEqualNP.CircuitLowerBounds T2OrPartition ThresholdOrExtraction ThresholdFlowPairs
open ThresholdSimpleIncidence ThresholdSharedPartition ThresholdSharedFlow ThresholdHubDegrees
open ThresholdWarmSimple ThresholdEffectiveColumns ThresholdColumnConflicts ThresholdSecondaryReceivers
open ThresholdHubFine ThresholdHighComponents ThresholdNativeColumnCharge
open T2CubeDeletion T2RegularOrDelete T2SoleOrSplice ThresholdRegularSource ResidualSurplus
open private hub_iff from ThresholdFlowSum
variable {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
local notation "Cir" => source gs out
local notation "Lay" => layout n gs out minim.eligible
local notation "HH" => high Lay
local notation "Hubs" => hubs Cir n

open private has_shared marked_hub from ThresholdNativeRowSelection

theorem original_anchor (r : Id Cir) (hr : r∈ThresholdNativeRowSelection.retained Lay) :
    ∃ S∈signature Cir n r,S∈Hubs ∧ S∈effective Lay minim r := by
  obtain ⟨S,sr,sh⟩ := has_shared Lay r hr
  refine ⟨S,sr,sh,Finset.mem_image.mpr ⟨S,sr,?_⟩⟩
  exact column_of_boundary Lay minim S (marked_hub S sh)

theorem high_room (b : Id Cir) (hb : b∈HH) (m e : Nat)
    (space : 2*((Hubs \ HH).card+m+e+1)≤(Hubs).card) :
    m+(missing Lay HH b).card+e<(HH).card := by
  classical
  let X := Hubs \ HH
  let N := neighbors Lay b
  let F := missing Lay HH b
  have sub : N⊆X∪(HH \ F) := by
    intro f hf
    obtain ⟨fg,ne,x,eq⟩ := Finset.mem_filter.mp hf
    by_cases h : f∈HH
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨h,fun bad => (Finset.mem_filter.mp bad).2
        ⟨ne,x,eq.trans (Finset.pair_comm _ _)⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨fg,h⟩)
  have gt : (Hubs).card<2*N.card := (Finset.mem_filter.mp hb).2
  have count := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have part := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ HH : F⊆HH)
  change (HH \ F).card+F.card=(HH).card at part
  change 2*(X.card+m+e+1)≤(Hubs).card at space
  change m+F.card+e<(HH).card
  omega

theorem marked_shared (r w : Id Cir) (ww : w∈effective Lay minim r) (m e : Nat)
    (miss : (missing Lay HH r).card≤m) (cold : (exceptional Lay minim HH r).card≤e)
    (room : m+e<(HH).card) : 2≤(readers Cir (n+w.val)).length := by
  classical
  have mark : boundary (n:=n) w := by
    obtain ⟨c,_,eq⟩ := Finset.mem_image.mp ww
    rw [←eq]; exact (trace_ok Lay minim c).2
  rcases mark with obs|shared
  · exfalso
    obtain ⟨f,hf,nm,nc⟩ : ∃ f∈HH,f∉missing Lay HH r ∧ f∉exceptional Lay minim HH r := by
      by_contra! bad
      have sub : HH⊆missing Lay HH r∪exceptional Lay minim HH r := by
        intro f h
        by_cases z : f∈missing Lay HH r
        · exact Finset.mem_union_left _ z
        · exact Finset.mem_union_right _ (bad f h z)
      have count := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
      omega
    obtain ⟨_,x,ed⟩ : Edge Lay f r := by simpa [missing,hf] using nm
    have hot : lit (C:=Cir) x w := by
      by_contra off
      exact nc (Finset.mem_filter.mpr ⟨hf,x,ed,w,ww,off⟩)
    unfold lit at hot
    rw [←obs] at hot
    have wrong := (minim.eligible.1 {x}).mp hot
    simp at wrong
  · exact shared

include reg in
theorem final_core (hn : 5≤n) (R : Finset (Id Cir)) (m e d u : Nat)
    (rows : ∀ r∈R,r∈good Cir n HH)
    (core : ThresholdColumnPeel.MinTwo (fun v r => v∈effective Lay minim r) R)
    (two : ∀ r∈R,(effective Lay minim r).card=2)
    (miss : ∀ r∈R,(missing Lay HH r).card≤m)
    (cold : ∀ r∈R,(exceptional Lay minim HH r).card≤e)
    (space : 2*((Hubs \ HH).card+m+e+1)≤(Hubs).card)
    (nonempty_room : m+e<(HH).card)
    (size : d+u=(Hubs).card) (loss : (Hubs \ HH).card+2*m+2*e≤u) :
    let T := R.biUnion (effective Lay minim)
    2*((d:ℤ)*(T.card:ℤ)+((inner Lay HH).card:ℤ))≤ThresholdHubFine.budget n (Cir).size := by
  classical
  intro T
  let O := T.filter (fun w => (Lay).op w=.or)
  let A := T \ O
  have any {w} (hw : w∈T) : ∃ c∈R,w∈effective Lay minim c := Finset.mem_biUnion.mp hw
  have mark {w} (hw : w∈T) : 2≤(readers Cir (n+w.val)).length := by
    obtain ⟨c,hr,h⟩ := any hw
    exact marked_shared minim c w h m e (miss c hr) (cold c hr) nonempty_room
  have subO : O⊆Hubs := by
    intro w hw
    obtain ⟨ht,op⟩ := Finset.mem_filter.mp hw
    exact (hub_iff Lay w).mpr ⟨by simpa [fan_readers] using mark ht,op⟩
  have andCost : A.card≤ThresholdSharedAndCredit.sharedAnd Lay := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨ht,no⟩ := Finset.mem_sdiff.mp hw
    have op : (Lay).op w=.and := by cases h : (Lay).op w <;> simp_all [O]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,op,by simpa [fan_readers] using mark ht⟩
  have outside : Disjoint O HH := by
    apply Finset.disjoint_left.mpr
    intro w hw
    obtain ⟨c,cr,inc⟩ := any (Finset.mem_filter.mp hw).1
    apply ThresholdNativeColumnCharge.outside_high minim reg c w (column_later minim (rows c cr) inc).ne inc
    have mc := miss c cr
    have ec := cold c cr
    omega
  have witness (w) (hw : w∈O) : ∃ a c v,a∈R ∧ c∈R ∧ a≠c ∧ effective Lay minim c={w,v} ∧ v∈effective Lay minim a := by
    obtain ⟨c,cr,inc⟩ := any (Finset.mem_filter.mp hw).1
    obtain ⟨p,q,ne,eq⟩ := Finset.card_eq_two.mp (two c cr)
    have other : ∃ v,effective Lay minim c={w,v} ∧ v∈effective Lay minim c := by
      rw [eq] at inc ⊢
      rcases Finset.mem_insert.mp inc with rfl|h
      · exact ⟨q,rfl,by simp⟩
      · obtain rfl := Finset.mem_singleton.mp h
        exact ⟨p,Finset.pair_comm _ _,by simp⟩
    obtain ⟨v,eqv,vc⟩ := other
    obtain ⟨a,ar,ac,av⟩ := core c cr v vc
    exact ⟨a,c,v,ar,cr,ac,eqv,av⟩
  let a (w : Id Cir) := if h : w∈O then (witness w h).choose else w
  let c (w : Id Cir) := if h : w∈O then (witness w h).choose_spec.choose else w
  let v (w : Id Cir) := if h : w∈O then (witness w h).choose_spec.choose_spec.choose else w
  have proof (w) (hw : w∈O) : a w∈R ∧ c w∈R ∧ a w≠c w ∧ effective Lay minim (c w)={w,v w} ∧ v w∈effective Lay minim (a w) := by
    simpa only [a,c,v,dif_pos hw] using (witness w hw).choose_spec.choose_spec.choose_spec
  have width := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ T : O⊆T)
  change (T \ O).card+O.card=T.card at width
  apply column_family minim reg hn HH O (Finset.filter_subset _ _) subO outside a c v u d A.card T.card size (by change T.card≤O.card+(T \ O).card; omega) andCost
  · intro w hw
    obtain ⟨_,cr,ne,eq,av⟩ := proof w hw
    exact ⟨ne,rows _ cr,eq,av⟩
  · intro w hw b hb
    have mc := miss _ (proof w hw).2.1
    have ec := cold _ (proof w hw).2.1
    have cap := high_room minim b hb m e space
    omega
  · intro w hw
    have ar := (proof w hw).1
    have cr := (proof w hw).2.1
    have cap := bad_count minim HH (a w) (c w)
    have ma := miss _ ar
    have mc := miss _ cr
    have ea := cold _ ar
    have ec := cold _ cr
    omega
include reg in
theorem selected_charge (hn : 5≤n)
    (select : 9*ThresholdNativeRowSelection.trimCost Lay<(HH).card^2)
    (t : Nat) (ht : t=(ThresholdNativeRowSelection.trimCost Lay).sqrt)
    (space : 2*((Hubs \ HH).card+t+t+1)≤(Hubs).card) (ready : t+t<(HH).card)
    (d : Nat) (size : d+((Hubs \ HH).card+2*t+2*t)=(Hubs).card) :
    ∃ K⊆ThresholdNativeRowSelection.retained Lay, ∃ R⊆K,
      ThresholdColumnPeel.MinTwo (fun v r => v∈signature Cir n r) K ∧
      ThresholdColumnPeel.MinTwo (fun v r => v∈effective Lay minim r) R ∧
      (∀ r∈R,(effective Lay minim r).card=2) ∧ Set.InjOn (effective Lay minim) (R : Set _) ∧
      (∀ r∈R,∃ S∈signature Cir n r,S∈Hubs ∧ S∈effective Lay minim r) ∧
      (HH).card≤R.card+(ThresholdPurityPins.impure Lay HH).card+ThresholdFlowSum.deltaO Lay+
        2*(ThresholdFanoutBudget.andIds Cir).length+(ThresholdNativeRowSelection.allPrivate Lay).card+
        t+2*(receivers Cir n HH).card ∧
      2*((d:ℤ)*((R.biUnion (effective Lay minim)).card:ℤ)+((inner Lay HH).card:ℤ))≤
        ThresholdHubFine.budget n (Cir).size := by
  subst t
  obtain ⟨K,ks,R,rs,orig,core,two,inj,row,card⟩ :=
    ThresholdNativeRowSelection.regular_selected hn minim reg select
  refine ⟨K,ks,R,rs,orig,core,two,inj,fun r hr => original_anchor minim r (ks (rs hr)),card,?_⟩
  exact final_core minim reg hn R _ _ d _ (fun r hr => (row r hr).1) core two
    (fun r hr => (row r hr).2.2.1) (fun r hr => (row r hr).2.2.2) space ready size le_rfl

#print axioms final_core
end ThresholdFinalCoreCharge
