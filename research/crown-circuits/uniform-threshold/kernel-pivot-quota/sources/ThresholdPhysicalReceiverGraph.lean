import ThresholdReceiverGraph
import ThresholdReceiverCollision
import ThresholdHubMissing
import ThresholdFamilySimpleGraph
namespace ThresholdPhysicalReceiverGraph
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction T2OrPartition
open ThresholdSimpleIncidence T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource
open ThresholdSecondaryReceivers ThresholdHighComponents ThresholdHubDegrees ThresholdC4Missing
open ThresholdSharedPartition
theorem high_common {C : Circuit} {n : Nat} (L : Layout C n)
    (u : Id C) (hu : u∈high L) (v : Id C) (hv : v∈high L) (ne : u≠v) :
    ∃ z x y, x≠y ∧ u∈endpoints L x ∧ z∈endpoints L x ∧
      v∈endpoints L y ∧ endpoints L y⊆{v,z} := by
  obtain ⟨z,zu,zv⟩ := shared_common L hu hv
  obtain ⟨_,zu,x,hx⟩ := Finset.mem_filter.mp zu
  obtain ⟨_,zv,y,hy⟩ := Finset.mem_filter.mp zv
  refine ⟨z,x,y,?_,by simp [hx],by simp [hx],by simp [hy],hy.le⟩
  intro eq
  have ux : u∈endpoints L y := eq ▸ (by simp [hx] : u∈endpoints L x)
  simpa [hy,ne,Ne.symm zu] using ux

variable {I : Type*} [DecidableEq I]
private def restrict (S : Finset I) (f : I → Finset I) (i : I) : Finset S :=
  Finset.univ.filter (fun z => z.val∈f i)

private theorem image_restrict (S : Finset I) (f : I→Finset I) {i : I}
    (sub : f i⊆S) : (restrict S f i).image Subtype.val=f i := by
  ext j
  constructor
  · rintro hj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp ha).2
  · intro hj
    exact Finset.mem_image.mpr ⟨⟨j,sub hj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩

private theorem image_union (S : Finset I) (f : I→Finset I) (p : Finset I)
    (sub : ∀ i∈p, f i⊆S) :
    (support (restrict S f) p).image Subtype.val=support f p := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i,hi,hj⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_biUnion.mpr ⟨i,hi,(Finset.mem_filter.mp hj).2⟩
  · intro hz
    obtain ⟨i,hi,hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_image.mpr ⟨⟨z,sub i hi hz⟩,Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩⟩,rfl⟩

local instance familyAdj {J : Type*} [DecidableEq J] (S : Finset J) (E : Finset (Finset J)) :
    DecidableRel (ThresholdFamilySimpleGraph.graph S E).Adj :=
  fun a b => inferInstanceAs (Decidable (a≠b ∧ {a.val,b.val}∈E))

theorem high_graph {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (hn : 2≤n) :
    let C := source gs out
    let L := layout n gs out M.eligible
    let H := high L
    let S := receivers C n H
    let E := edgeFamily C n H
    let G := ThresholdFamilySimpleGraph.graph S E
    let A := (Finset.univ : Finset (Fin n)).image (endpoints L)
    G.edgeFinset.card=(good C n H).card ∧
      ThresholdC4.ordered G ≤24*(missing (good C n H) A).card := by
  classical
  intro C L H S E G A
  have hub : H⊆hubs C n := Finset.filter_subset _ _
  obtain ⟨edgecount,shape⟩ := receiver_graph M reg hn H hub (high_common L)
  refine ⟨(ThresholdFamilySimpleGraph.edge_card S E shape).trans edgecount,?_⟩
  let f := signature C n
  have sub (i : Id C) (hi : i∈good C n H) : f i⊆S :=
    fun j hj => Finset.mem_biUnion.mpr ⟨i,hi,hj⟩
  apply ordered_le G (good C n H) (restrict S f) A
  · intro i hi
    have h : f i∈E := Finset.mem_image.mpr ⟨i,hi,rfl⟩
    have two := (Finset.mem_powersetCard.mp (shape h)).2
    have eq := congrArg Finset.card (image_restrict S f (sub i hi))
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at eq
    omega
  · intro x y h
    have pair : {x.val,y.val}∈E := h.2
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp pair
    refine ⟨i,hi,?_⟩
    ext z
    have ef : f i={x.val,y.val} := eq
    simp only [restrict,Finset.mem_filter,Finset.mem_univ,true_and,ef,
      Finset.mem_insert,Finset.mem_singleton]
    constructor
    · exact fun h => h.imp Subtype.ext Subtype.ext
    · exact fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)
  · intro p hp q hq gp gq eq
    have whole := congrArg (Finset.image (fun j : ↥S => j.val)) eq
    rw [image_union S f p (fun i hi => sub i (gp hi)),
        image_union S f q (fun i hi => sub i (gq hi))] at whole
    exact ThresholdReceiverCollision.union_injective M reg H p hp q hq gp whole

theorem missing_global {C : Circuit} {n : Nat} (L : Layout C n)
    (two : ∀ x, (endpoints L x).card=2) (inj : Function.Injective (endpoints L))
    (labels : Finset (Id C)) (sub : labels⊆hubs C n) :
    (missing labels ((Finset.univ : Finset (Fin n)).image (endpoints L))).card ≤
      ThresholdHubMissing.M L := by
  classical
  let H := hubs C n
  let A := (Finset.univ : Finset (Fin n)).image (endpoints L)
  let B := (internal L).image (endpoints L)
  have small : B⊆H.powersetCard 2 := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    have ht : 2≤(hits L i).card := (Finset.mem_filter.mp hi).2
    have eq : hits L i=endpoints L i := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [two]; exact ht)
    exact Finset.mem_powersetCard.mpr ⟨eq ▸ (Finset.inter_subset_right : hits L i⊆H),two i⟩
  have incl : missing labels A ⊆ H.powersetCard 2 \ B := by
    intro p hp
    obtain ⟨mem,abs⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨ps,card⟩ := Finset.mem_powersetCard.mp mem
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨fun i hi => sub (ps hi),card⟩,?_⟩
    intro hb
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hb
    exact abs (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq⟩)
  have le := Finset.card_le_card incl
  rw [Finset.card_sdiff_of_subset small,Finset.card_powersetCard,
      show B.card=(internal L).card from Finset.card_image_of_injective _ inj] at le
  exact le

end ThresholdPhysicalReceiverGraph
