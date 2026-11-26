import ThresholdPhysicalIdeals
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
namespace ThresholdHighComponents
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence
open ThresholdHubDegrees ThresholdGraphCounts ThresholdSharedPartition T2OrPartition
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def high := (hubs C n).filter (fun u => (hubs C n).card<2*(neighbors L u).card)

theorem shared_common {u v : Id C} (hu : u∈high L) (hv : v∈high L) :
    ∃ w,w∈neighbors L u ∧ w∈neighbors L v := by
  classical
  by_contra! none
  have dis := Finset.disjoint_left.mpr none
  have cap := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ (hubs C n))
    (Finset.filter_subset _ (hubs C n)) : neighbors L u∪neighbors L v⊆hubs C n)
  rw [Finset.card_union_of_disjoint dis] at cap
  have ua := (Finset.mem_filter.mp hu).2
  have va := (Finset.mem_filter.mp hv).2
  omega

theorem edge_component (x : Fin n) (a b : Id C) (ax : a∈endpoints L x) (bx : b∈endpoints L x) :
    (graph L).connectedComponentMk ⟨a,active_endpoint L x ax⟩ =
      (graph L).connectedComponentMk ⟨b,active_endpoint L x bx⟩ := by
  by_cases e : a=b
  · subst b; rfl
  · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    exact ⟨fun h => e (congrArg Subtype.val h),x,ax,bx⟩

theorem high_component (a b : Vtx L) (ha : a.val∈high L) (hb : b.val∈high L) :
    (graph L).connectedComponentMk a=(graph L).connectedComponentMk b := by
  obtain ⟨w,aw,bw⟩ := shared_common L ha hb
  obtain ⟨_,_,x,ax⟩ := Finset.mem_filter.mp aw
  obtain ⟨_,_,y,by'⟩ := Finset.mem_filter.mp bw
  exact (edge_component L x a.val w (by simp [ax]) (by simp [ax])).trans
    (edge_component L y w b.val (by simp [by']) (by simp [by']))

theorem component_bound (two : ∀ x,(endpoints L x).card=2) :
    Nat.card (graph L).ConnectedComponent ≤ 1+((hubs C n) \ high L).card+(missed L).card := by
  classical
  let G := graph L
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let A := ((hubs C n) \ high L).filter (fun u => u∈vertices L)
  let pick (x : Fin n) : Vtx L :=
    let h := Finset.card_pos.mp (show 0<(endpoints L x).card by rw [two]; decide)
    ⟨h.choose,active_endpoint L x h.choose_spec⟩
  have pick_mem (x : Fin n) : (pick x).val∈endpoints L x := by
    dsimp only [pick]
    exact Exists.choose_spec _
  let small := A.attach.image (fun a => G.connectedComponentMk
    (⟨a.val,(Finset.mem_filter.mp a.property).2⟩ : Vtx L))
  let free := (missed L).image (fun x => G.connectedComponentMk (pick x))
  let big := (Finset.univ.filter (fun v : Vtx L => v.val∈high L)).image G.connectedComponentMk
  have highOne : big.card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨a,ha,eq₁⟩ := Finset.mem_image.mp hi
    obtain ⟨b,hb,eq₂⟩ := Finset.mem_image.mp hj
    rw [←eq₁,←eq₂]
    exact high_component L a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have cover : (Finset.univ : Finset G.ConnectedComponent)⊆big∪small∪free := by
    intro c _
    obtain ⟨v,rfl⟩ := c.exists_rep
    obtain ⟨x,hx⟩ := rawAt_nonempty L v
    have vx : v.val∈endpoints L x := (Finset.mem_filter.mp hx).2
    by_cases h : (hits L x).Nonempty
    · obtain ⟨a,ha⟩ := h
      obtain ⟨ax,hub⟩ := Finset.mem_inter.mp ha
      let b : Vtx L := ⟨a,active_endpoint L x ax⟩
      have same : G.connectedComponentMk b=G.connectedComponentMk v := edge_component L x a v.val ax vx
      apply Finset.mem_union_left
      by_cases hi : a∈high L
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,same⟩)
      · have am : a∈A := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hub,hi⟩,b.property⟩
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨a,am⟩,Finset.mem_attach _ _,same⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.not_nonempty_iff_eq_empty.mp h⟩,
        edge_component L x (pick x).val v.val (pick_mem x) vx⟩
  have all := Finset.card_le_card cover
  have c1 := Finset.card_union_le big small
  have c2 := Finset.card_union_le (big∪small) free
  have costS : small.card≤A.card := by simpa [small] using (Finset.card_image_le (s:=A.attach)
    (f:=fun a => G.connectedComponentMk (⟨a.val,(Finset.mem_filter.mp a.property).2⟩ : Vtx L)))
  have costF : free.card≤(missed L).card := Finset.card_image_le
  have costA : A.card≤((hubs C n) \ high L).card := Finset.card_le_card (Finset.filter_subset _ _)
  change Nat.card G.ConnectedComponent≤_
  rw [Nat.card_eq_fintype_card]
  simp only [Finset.card_univ] at all
  omega
#print axioms component_bound
end ThresholdHighComponents
