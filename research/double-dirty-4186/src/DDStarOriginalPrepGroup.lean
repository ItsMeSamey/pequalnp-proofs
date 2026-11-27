import DDStarOverlap
import Q1DoublePrivatePhysical
import DDOneLeakCut
import Q1DoublePhysicalPrice

-- Source: DDStarOriginalBatches.lean (sha256 f60d32c19f0bb12b8fad3fa262c646281ed3b6d66c1c1ef0b18bc9403b2212ac)
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Allocation Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
abbrev Pin := ℕ × Fin 2

noncomputable def shareIndex (A Y : Finset Pin) (i : Fin (A∩Y).card) : Fin A.card :=
  A.equivFin ⟨((A∩Y).equivFin.symm i).val,(Finset.mem_inter.mp ((A∩Y).equivFin.symm i).property).1⟩

theorem shareIndex_support (A Y : Finset Pin) :
    indexedLeaf n C A ∘ shareIndex A Y = indexedLeaf n C (A∩Y) := by
  funext i; simp [indexedLeaf,shareIndex,Function.comp_def]

theorem original_external_batch (s : OriginalCut G C) (data : GroupData s) {t : ℕ}
    (gmem : t∈s.group) (ne : t≠s.top) (A : Finset Pin) :
    ∃ Y : Private.Batch G C (indexedLeaf n C A ∘ shareIndex A (leaves n C t))
        (indexedLeaf n C (leaves n C t \ A)) (data.own t).card,
      ∀ i, ((data.own t).equivFin.symm i).val = s(Y.pt i false,Y.pt i true) := by
  classical
  have ht : t∈tops G C := (Finset.mem_filter.mp (s.group_sub gmem)).1
  have tr := Finset.mem_filter.mp ht
  obtain ⟨q,_,unique⟩ := unique_influenced_top s.double s.edge s.least s.form
  have root := unique s.top ⟨(Finset.mem_filter.mp s.centrelessTop).1,s.influence⟩
  have away : ¬Influence n C s.mixer (n+t) := fun h => ne ((unique t ⟨ht,h⟩).trans root.symm)
  let T := leaves n C t
  let K := A ∩ T
  let Z := T \ A
  have join : K ∪ Z = T := by ext p; simp [K,Z]; tauto
  have plain := external_plain s.least.1 away
  have desc : ClauseSignal G C (gateVal n C t) (indexedLeaf n C K) (indexedLeaf n C Z) := by
    apply physicalDesc s.double s.four s.least
    · rw [join]; exact plain
    · intro x
      rw [region_clause_semantics s.double s.least.1 s.form (Finset.mem_range.mp tr.1) tr.2.1 plain x]
      change (∀ p∈T, _) ↔ _
      conv_lhs => rw [← join]
      simp only [Finset.forall_mem_union]
  have resid : data.own t⊆Ustar G C := by
    intro e he
    apply data.res
    rw [data.edges]
    exact Finset.mem_biUnion.mpr ⟨t,gmem,he⟩
  have acc (e) (he:e∈data.own t) : AcceptPair (gateVal n C t) e := by
    obtain ⟨_,a,b,hs,hv⟩ := Finset.mem_filter.mp (data.accepted t he)
    exact ⟨a,b,hs,hv⟩
  rw [shareIndex_support]
  exact Private.batch_of_signal s.four _ _ (data.own t) resid _ acc tr.2.2 desc.semantics desc.anchor

structure CentralBatches (s : OriginalCut G C) (data : GroupData s) (a b : ℕ) where
  pin : Pin
  used : pin∈leaves n C s.top
  guard : 0<((leaves n C s.top).erase pin).card
  le : Finset (Sym2 (Fin n))
  ri : Finset (Sym2 (Fin n))
  dis : Disjoint le ri
  union : le∪ri=data.own s.top
  counts : le.card+ri.card=(data.own s.top).card
  lp : Private.Batch G C (indexedLeaf n C (leaves n C a))
    (indexedLeaf n C ((leaves n C s.top).erase pin)) le.card
  rp : Private.Batch G C (indexedLeaf n C (leaves n C b))
    (indexedLeaf n C ((leaves n C s.top).erase pin)) ri.card
  llab : ∀ i, (le.equivFin.symm i).val=s(lp.pt i false,lp.pt i true)
  rlab : ∀ i, (ri.equivFin.symm i).val=s(rp.pt i false,rp.pt i true)

theorem original_central_batches (s : OriginalCut G C) (data : GroupData s) (a b : ℕ)
    (sides : (a=s.left ∧ b=s.right) ∨ (a=s.right ∧ b=s.left)) :
    Nonempty (CentralBatches s data a b) := by
  classical
  have ht : s.top∈tops G C := (Finset.mem_filter.mp s.centrelessTop).1
  have ownResid : data.own s.top ⊆ Ustar G C := by
    intro e he
    apply data.res
    rw [data.edges]
    exact Finset.mem_biUnion.mpr ⟨s.top,by simp [group],he⟩
  obtain ⟨pin,hp,_,ne,_,plainW,guard⟩ :=
    guard_clause_decomposition s.double s.edge s.least s.form ht s.influence
  let W := (leaves n C s.top).erase pin
  let term (j : ℕ) := fun x => gateVal n C j x && clauseConjunction n C W x
  have arms (j : ℕ) (dirty : j∈junk G C) (jpin : n+j∈(gateAt C s.mixer).inputs) :
      ClauseSignal G C (term j) (indexedLeaf n C (leaves n C j)) (indexedLeaf n C W) := by
    obtain ⟨jl,jo,_⟩ := (S4183.junk_iff G C j).mp dirty
    have plain := arm_boundary_plain s.double s.least.1 jpin
    apply physicalDesc s.double s.four s.least
    · intro p h
      exact (Finset.mem_union.mp h).elim (plain p) (plainW p)
    · intro x
      simp only [term,Bool.and_eq_true]
      rw [region_clause_semantics s.double s.least.1 s.form jl jo plain x]
      simp [clauseConjunction]
  have memL : n+s.left∈(gateAt C s.mixer).inputs := by simp [s.pins]
  have memR : n+s.right∈(gateAt C s.mixer).inputs := by simp [s.pins]
  have split (x) : gateVal n C s.top x=(term a x || term b x) := by
    obtain ⟨hm,op,_⟩ := mixer_info s.double
    have mix := W_or n C x s.mixer hm op _ _ s.pins (s.least.1.2.1 _ hm _ memL) (s.least.1.2.1 _ hm _ memR)
    change gateVal n C s.mixer x=(gateVal n C s.left x || gateVal n C s.right x) at mix
    rw [guard x,mix]
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      cases en : clauseConjunction n C W x <;> simp [term,W] at en ⊢ <;> simp [en,Bool.or_comm]
  obtain ⟨L,R,dis,un,card,ownsL,ownsR⟩ := partitionProjected G C _ (data.accepted _) _ _ split
  have below := (Finset.mem_filter.mp ht).2.2
  have construct {j} (E : Finset (Sym2 (Fin n))) (sub : E⊆data.own s.top) (owns : ∀ e∈E, AcceptPair (term j) e)
      (desc : ClauseSignal G C (term j) (indexedLeaf n C (leaves n C j)) (indexedLeaf n C W))
      (clean : ∀ x, term j x=true → graphFun G ∅ x=true) :=
    Private.batch_of_signal s.four _ _ E (sub.trans ownResid) _ owns clean desc.semantics desc.anchor
  have descA : ClauseSignal G C (term a) (indexedLeaf n C (leaves n C a)) (indexedLeaf n C W) := by
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> first | exact arms _ s.leftDirty memL | exact arms _ s.rightDirty memR
  have descB : ClauseSignal G C (term b) (indexedLeaf n C (leaves n C b)) (indexedLeaf n C W) := by
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> first | exact arms _ s.leftDirty memL | exact arms _ s.rightDirty memR
  obtain ⟨pl,hl⟩ := construct L (un ▸ Finset.subset_union_left) ownsL descA (fun x yes => below x (by simp [split,yes]))
  obtain ⟨pr,hr⟩ := construct R (un ▸ Finset.subset_union_right) ownsR descB (fun x yes => below x (by simp [split,yes]))
  exact ⟨⟨pin,hp,Finset.card_pos.mpr ne,L,R,dis,un,card,pl,pr,hl,hr⟩⟩
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut

-- Source: DDStarOriginalPrice.lean (sha256 3119dde04e4d77a62116332ee179c19f5cbffeaffd0b6701e6f44fa850a9c43e)
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor
open scoped BigOperators
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem star_price (s : OriginalCut G C) (a b : ℕ)
    (sides : (a=s.left ∧ b=s.right) ∨ (a=s.right ∧ b=s.left))
    (one : s.ArmSingle a) (emptyB : externalLabels G C s.top b=∅)
    (pin : ℕ × Fin 2) (used : pin ∈ leaves n C s.top) :
    (leaves n C a).card + (leaves n C b).card + ((leaves n C s.top).erase pin).card +
      ∑ t ∈ externalLabels G C s.top a, ((leaves n C t \ leaves n C a).card+1) ≤
      s.groupPool.card + 2*s.group.card + 1 := by
  classical
  let I := externalLabels G C s.top a
  let A := andRegion n C a
  let B := andRegion n C b
  let W := interior n C s.top
  let E := fun t => ((andRegion n C t) \ A).erase t
  have ao := s.least.1
  have ha : a ∈ junk G C := sides.elim (fun h => h.1 ▸ s.leftDirty) (fun h => h.1 ▸ s.rightDirty)
  have hb : b ∈ junk G C := sides.elim (fun h => h.2 ▸ s.rightDirty) (fun h => h.2 ▸ s.leftDirty)
  have armEq : A ∪ B = s.armPool := by rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [A,B,armPool,Finset.union_comm]
  have ab : Disjoint A B := by
    have dis := arm_regions_disjoint s.double s.edge s.least s.form
      (show opnd C s.mixer 0=n+s.left by simp [opnd,s.pins])
      (show opnd C s.mixer 1=n+s.right by simp [opnd,s.pins])
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact dis
    · exact dis.symm
  have gEq : s.group=insert s.top I := by
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [group,L,R,I,emptyB]
  have membership {t} (ht : t∈I) : t∈(centreless G C).erase s.top := (Finset.mem_filter.mp ht).1
  have real {t} (ht : t∈I) : t∈tops G C :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase (membership ht))).1
  have interiorSub {t} : E t ⊆ interior n C t := by
    intro g hg
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hg
    exact Finset.mem_erase.mpr ⟨ne,(Finset.mem_sdiff.mp mem).1⟩
  have noB {t} (ht : t∈I) : Disjoint B (interior n C t) := by
    by_contra wrong
    have hx : t ∈ externalLabels G C s.top b := Finset.mem_filter.mpr ⟨membership ht,wrong⟩
    simpa [emptyB] using hx
  have guard := guard_arm_disjoint s.double s.edge s.least s.form
    (Finset.mem_filter.mp s.centrelessTop).1 s.influence s.pins
  have gw : Disjoint (A∪B) W := armEq ▸ guard
  have disgw {t} (ht : t∈I) : Disjoint W (interior n C t) := by
    apply exteriorDisjoint s.double s.edge s.least s.form (Finset.mem_filter.mp s.centrelessTop).1
      (real ht) (Finset.mem_erase.mp (membership ht)).1.symm
    intro g gw' _ w hw path
    have op := in_region.mp (Finset.mem_of_mem_erase gw')
    apply fun h => Finset.disjoint_left.mp guard h gw'
    rw [s.pins] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact Finset.mem_union_left _ (in_region.mpr ⟨op.1,op.2.1,path⟩)
    · exact Finset.mem_union_right _ (in_region.mpr ⟨op.1,op.2.1,path⟩)
  have localBound (t) (ht : t∈I) : (leaves n C t \ leaves n C a).card+1 ≤ (E t).card+2 := by
    have tr := Finset.mem_filter.mp (real ht)
    have rt := root_mem_region (n:=n) (Finset.mem_range.mp tr.1) tr.2.1
    have notin : t∉A := fun h => ((S4183.junk_iff G C t).mp (dirty_region_sub ao s.form ha h)).2.2 tr.2.2
    obtain ⟨g,hga,hgt⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp ht).2
    have share : (andRegion n C a ∩ andRegion n C t).Nonempty :=
      ⟨g,Finset.mem_inter.mpr ⟨hga,Finset.mem_of_mem_erase hgt⟩⟩
    have p := OneLeak.private_width ao rt notin share
    change (leaves n C t \ leaves n C a).card ≤ (andRegion n C t \ A).card at p
    have e := Finset.card_erase_add_one (a:=t) (Finset.mem_sdiff.mpr ⟨rt,notin⟩)
    change (E t).card + 1 = _ at e
    omega
  have exdis : (I : Set ℕ).PairwiseDisjoint E :=
    fun i hi j hj ne => (star_ext_disjoint s sides one emptyB (membership hi) (membership hj) ne).mono
      interiorSub interiorSub
  have allDis : Disjoint (A∪B∪W) (I.biUnion E) := by
    apply Finset.disjoint_left.mpr
    intro g gin gex
    obtain ⟨t,ht,mem⟩ := Finset.mem_biUnion.mp gex
    rcases Finset.mem_union.mp gin with arm|gw'
    · rcases Finset.mem_union.mp arm with ga|gb
      · exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase mem)).2 ga
      · exact Finset.disjoint_left.mp (noB ht) gb (interiorSub mem)
    · exact Finset.disjoint_left.mp (disgw ht) gw' (interiorSub mem)
  have sub : A∪B∪W∪I.biUnion E ⊆ s.groupPool := by
    intro g hg
    rw [groupPool]
    rcases Finset.mem_union.mp hg with abw|outside
    · rcases Finset.mem_union.mp abw with ab'|gw'
      · exact Finset.mem_union_left _ (armEq ▸ ab')
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s.top,by simp [gEq],gw'⟩)
    · obtain ⟨t,ht,mem⟩ := Finset.mem_biUnion.mp outside
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,by simp [gEq,ht],interiorSub mem⟩)
  have count := physical_region_bound I A B W s.groupPool E exdis ab gw allDis sub
  have gsize : I.card+1 ≤ s.group.card := by
    have no : s.top ∉ I := fun h => (Finset.mem_erase.mp (membership h)).1 rfl
    simp [gEq,no]
  have hh := Finset.mem_filter.mp ((Finset.mem_filter.mp s.centrelessTop).1 : s.top∈tops G C)
  have gwc := guard_occurrences n C (andRegion n C s.top) s.top
    (root_mem_region (Finset.mem_range.mp hh.1) hh.2.1) (region_used ao _) pin used
  have hl := (S4183.junk_iff G C a).mp ha
  have hr := (S4183.junk_iff G C b).mp hb
  exact mixer_allowance I _ _ _ A.card B.card W.card (fun t => (leaves n C t \ leaves n C a).card)
    (fun _ => 1) (fun t => (E t).card) _ _ (region_occurrences_bound ao hl.1 hl.2.1)
    (region_occurrences_bound ao hr.1 hr.2.1) gwc localBound count gsize
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
