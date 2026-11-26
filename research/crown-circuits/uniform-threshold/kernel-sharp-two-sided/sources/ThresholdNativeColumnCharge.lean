import ThresholdColumnConflicts
import ThresholdEffectiveColumnBudget
namespace ThresholdNativeColumnCharge
open PEqualNP.CircuitLowerBounds T2OrPartition ThresholdOrExtraction ThresholdFlowPairs
open ThresholdSimpleIncidence ThresholdSharedPartition ThresholdSharedFlow
open ThresholdColumnConflicts ThresholdWarmSimple ThresholdEffectiveColumns
open ThresholdSecondaryReceivers ThresholdHubFine ThresholdHighComponents
open T2CubeDeletion T2RegularOrDelete T2SoleOrSplice ThresholdRegularSource ResidualSurplus
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def unspent := ((hubs C n).powersetCard 2) \
  ((hotPairs L).image unordered ∪ (internal L).image (endpoints L))
theorem card_unspent (card : ∀ e, (endpoints L e).card=2)
    (inj : Function.Injective (endpoints L))
    (noedge : ∀ u∈hubs C n, ∀ v∈hubs C n, u≠v → active L u v=true →
      ∀ e : Fin n, u∈endpoints L e → v∉endpoints L e) :
    (unspent L).card=ThresholdHubMissing.q L := by
  classical
  let H := hubs C n
  let A := (hotPairs L).image unordered
  let B := (internal L).image (endpoints L)
  have hp {p : Id C × Id C} (h : p∈hotPairs L) :
      (p.1∈H ∧ p.2∈H) ∧ p.1≠p.2 ∧ active L p.1 p.2=true := by simpa [hotPairs,H] using h
  have uniqueA : Set.InjOn (unordered (C:=C)) ((hotPairs L) : Set (Id C × Id C)) := by
    rintro ⟨a,b⟩ h ⟨x,y⟩ k eq
    have lt := oriented L (hp h).2.1 (hp h).2.2
    have lt' := oriented L (hp k).2.1 (hp k).2.2
    have hax : a=x ∨ a=y := by
      have z : a∈unordered (x,y) := eq ▸ (by simp [unordered] : a∈unordered (a,b))
      simpa [unordered] using z
    have hby : b=x ∨ b=y := by
      have z : b∈unordered (x,y) := eq ▸ (by simp [unordered] : b∈unordered (a,b))
      simpa [unordered] using z
    change a<b at lt
    change x<y at lt'
    rcases hax with ax|ay <;> rcases hby with bx|byy
    · exact False.elim (lt.ne (ax.trans bx.symm))
    · exact Prod.ext ax byy
    · have rev : b<a := by rw [bx,ay]; exact lt'
      exact False.elim (lt_asymm lt rev)
    · exact False.elim (lt.ne (ay.trans byy.symm))
  have internalH {e : Fin n} (he : e∈internal L) : endpoints L e ⊆ H := by
    have two : 2≤(hits L e).card := (Finset.mem_filter.mp he).2
    have eq : hits L e=endpoints L e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [card]; exact two)
    exact eq ▸ (Finset.inter_subset_right : hits L e⊆H)
  have sub : A ∪ B ⊆ H.powersetCard 2 := by
    intro t ht
    rcases Finset.mem_union.mp ht with ha|hb
    · obtain ⟨p,hp',rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset (hp hp').1.1
        (Finset.singleton_subset_iff.mpr (hp hp').1.2),Finset.card_pair_eq_two_iff.mpr (hp hp').2.1⟩
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_powersetCard.mpr ⟨internalH he,card e⟩
  have disj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro t hA hB
    obtain ⟨p,hp',ep⟩ := Finset.mem_image.mp hA
    obtain ⟨e,_,ee⟩ := Finset.mem_image.mp hB
    have eq := ee.trans ep.symm
    exact noedge p.1 (hp hp').1.1 p.2 (hp hp').1.2 (hp hp').2.1 (hp hp').2.2 e (by simp [eq,unordered]) (by simp [eq,unordered])
  have count := Finset.card_sdiff_add_card_eq_card sub
  change (unspent L).card+(A∪B).card=(H.powersetCard 2).card at count
  rw [Finset.card_union_of_disjoint disj,Finset.card_powersetCard] at count
  simp only [A,B,Finset.card_image_of_injOn uniqueA,Finset.card_image_of_injective _ inj] at count
  change (unspent L).card = H.card.choose 2-(internal L).card-(hotPairs L).card
  omega

theorem genuinely_free {f w : Id C} (hf : f∈hubs C n) (hw : w∈hubs C n) (ne : f≠w)
    (raw : ¬Edge L f w) (inc : active L f w≠true) (out : active L w f≠true) :
    ({w,f} : Finset (Id C))∈unspent L := by
  classical
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hw (Finset.singleton_subset_iff.mpr hf),
    Finset.card_pair_eq_two_iff.mpr ne.symm⟩,?_⟩
  intro mem
  rcases Finset.mem_union.mp mem with hot|edge
  · obtain ⟨p,ph,eq⟩ := Finset.mem_image.mp hot
    have info := (ThresholdPhysicalIdeals.mem_pair L p.1 p.2).mp ph
    have a : p.1=w ∨ p.1=f := by have h : p.1∈({w,f}:Finset _) := eq ▸ (by simp [unordered] : p.1∈unordered p); simpa using h
    have b : p.2=w ∨ p.2=f := by have h : p.2∈({w,f}:Finset _) := eq ▸ (by simp [unordered] : p.2∈unordered p); simpa using h
    rcases a with a|a <;> rcases b with b|b <;> grind
  · obtain ⟨x,_,xe⟩ := Finset.mem_image.mp edge
    exact raw ⟨ne,x,xe.trans (Finset.pair_comm _ _)⟩

noncomputable def inner (H : Finset (Id C)) := (unspent L).filter (fun e => e⊆H)

section
variable {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
local notation "C" => source gs out
local notation "L" => layout n gs out minim.eligible
noncomputable def bad (H : Finset (Id C)) (a c : Id C) :=
  (missing L H a ∪ missing L H c) ∪ (exceptional L minim H a ∪ exceptional L minim H c)

include reg in
theorem cross_native (H : Finset (Id C)) (hs : H⊆hubs C n) (a c w v : Id C)
    (apart : a≠c) (wh : w∈hubs C n) (outside : w∉H)
    (goodC : c∈good C n H) (wc : effective L minim c={w,v}) (av : v∈effective L minim a)
    (room : ∀ b∈H,(missing L H c).card+(missing L H b).card+(exceptional L minim H c).card<H.card)
    (f : Id C) (hf : f∈H \ bad minim H a c) : ({w,f}:Finset _)∈unspent L := by
  classical
  obtain ⟨inH,ok⟩ := Finset.mem_sdiff.mp hf
  have cw : w∈effective L minim c := by simp [wc]
  have ne := (column_later minim goodC cw).ne
  have noRaw : ¬Edge L f w := by
    intro edge
    have z := neighbors_bad minim reg H c w ne cw (Finset.mem_filter.mpr ⟨inH,edge⟩)
    rcases Finset.mem_union.mp z with z|z <;> exact ok (by simp [bad,z])
  have noInc : active L f w≠true := by
    intro on
    have z := incoming_bad minim reg H a c w v apart wc av (Finset.mem_filter.mpr ⟨inH,on⟩)
    rcases Finset.mem_union.mp z with z|z
    · rcases Finset.mem_union.mp z with z|z <;> exact ok (by simp [bad,z])
    · exact ok (by simp [bad,z])
  exact genuinely_free L (hs inH) wh (fun e => outside (e ▸ inH)) noRaw noInc
    (outgoing_none minim reg H c w f goodC cw (room f inH))

include reg in
theorem outside_high (a w : Id C) (apart : a≠w) (inc : w∈effective L minim a)
    (room : 2*(((hubs C n) \ high L).card+(missing L (high L) a).card+
      (exceptional L minim (high L) a).card)≤(hubs C n).card) : w∉high L := by
  classical
  let H := high L
  let G := hubs C n
  let X := G \ H
  let Y := missing L H a ∪ exceptional L minim H a
  have sub : ThresholdHubDegrees.neighbors L w ⊆ X∪Y := by
    intro f hf
    obtain ⟨fg,ne,x,xe⟩ := Finset.mem_filter.mp hf
    by_cases fh : f∈H
    · apply Finset.mem_union_right
      apply neighbors_bad minim reg H a w apart inc
      exact Finset.mem_filter.mpr ⟨fh,ne,x,xe.trans (Finset.pair_comm w f)⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨fg,fh⟩)
  have few := Finset.card_le_card sub
  have xy := Finset.card_union_le X Y
  have yy : Y.card≤(missing L H a).card+(exceptional L minim H a).card := Finset.card_union_le _ _
  intro hi
  have gt : G.card<2*(ThresholdHubDegrees.neighbors L w).card := (Finset.mem_filter.mp hi).2
  change 2*(X.card+(missing L H a).card+(exceptional L minim H a).card)≤G.card at room
  omega

theorem bad_count (H : Finset (Id C)) (a c : Id C) :
    (bad minim H a c).card≤(missing L H a).card+(missing L H c).card+
      (exceptional L minim H a).card+(exceptional L minim H c).card := by
  unfold bad
  exact (Finset.card_union_le _ _).trans (by
    have left := Finset.card_union_le (missing L H a) (missing L H c)
    have right := Finset.card_union_le (exceptional L minim H a) (exceptional L minim H c)
    omega)

include reg in
theorem column_family (hn : 5≤n) (H O : Finset (Id C)) (subH : H⊆hubs C n)
    (subO : O⊆hubs C n) (outside : Disjoint O H)
    (a c v : Id C→Id C) (u d andCols wCount : Nat)
    (size : d+u=(hubs C n).card) (width : wCount≤O.card+andCols)
    (andCost : andCols≤ThresholdSharedAndCredit.sharedAnd L)
    (family : ∀ w∈O,a w≠c w ∧ c w∈good C n H ∧ effective L minim (c w)={w,v w} ∧
      v w∈effective L minim (a w))
    (room : ∀ w∈O,∀ b∈H,(missing L H (c w)).card+(missing L H b).card+
      (exceptional L minim H (c w)).card<H.card)
    (loss : ∀ w∈O,((hubs C n) \ H).card+(bad minim H (a w) (c w)).card≤u) :
    2*((d:ℤ)*(wCount:ℤ)+((inner L H).card:ℤ))≤ThresholdHubFine.budget n (C).size := by
  classical
  let G := hubs C n
  let choices := fun w => H \ bad minim H (a w) (c w)
  have one w (hw : w∈O) f (hf : f∈choices w) := cross_native minim reg H subH (a w) (c w) w
    (v w) (family w hw).1 (subO hw) (Finset.disjoint_left.mp outside hw)
    (family w hw).2.1 (family w hw).2.2.1 (family w hw).2.2.2 (room w hw) f hf
  have many w (hw : w∈O) : d≤(choices w).card := by
    have sub : bad minim H (a w) (c w)⊆H := by
      intro f hf
      simp only [bad,Finset.mem_union] at hf
      rcases hf with (z|z)|(z|z) <;> exact (Finset.mem_filter.mp z).1
    have cut := Finset.card_sdiff_add_card_eq_card sub
    have gap := Finset.card_sdiff_add_card_eq_card subH
    have ok := loss w hw
    change d≤(H \ bad minim H (a w) (c w)).card
    omega
  have charge := ThresholdEffectiveColumnBudget.cross_charge H O (unspent L) (inner L H)
    choices outside (fun _ he => (Finset.mem_filter.mp he).2) (Finset.filter_subset _ _)
    (fun _ _ _ mem => (Finset.mem_sdiff.mp mem).1) one d many
  have simple := classified_simple (by omega : 2≤n) minim reg
  have st := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out minim reg
  rw [card_unspent L simple.1 simple.2.1 st.no_shared_raw] at charge
  have credit := ThresholdSharedAndCredit.regular_credit hn minim reg
  change 2*((ThresholdHubMissing.q L:ℤ)+((hubs C n).card:ℤ)*(ThresholdSharedAndCredit.sharedAnd L:ℤ))≤ThresholdHubFine.budget n (C).size at credit
  have mul := Nat.mul_le_mul_left d width
  have cost := Nat.mul_le_mul (show d≤(hubs C n).card by omega) andCost
  zify at charge mul cost
  nlinarith only [charge,mul,cost,credit]
#print axioms column_family
end
end ThresholdNativeColumnCharge
