import DDStarOriginalPrepGroup
import Q1DoubleStarPhysical
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Allocation
open scoped BigOperators
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem oriented_mem {E : Finset (Sym2 (Fin n))} {pt : Fin E.card → Bool → Fin n}
    (lab : ∀ i, (E.equivFin.symm i).val=s(pt i false,pt i true)) (i : Fin E.card) (b : Bool) :
    s(pt i b,pt i (!b))∈E := by
  have h := (E.equivFin.symm i).property
  rw [lab i] at h
  cases b
  · exact h
  · exact Sym2.eq_swap ▸ h

/-- The full one-arm budget in the original circuit. The single-incidence
premise is the projection of the split two-root cap; no subcone equality
or uniqueness of a branch for a given external top is used. -/
theorem completeOneArmMany (s : OriginalCut G C) (a b : ℕ)
    (sides : (a=s.left ∧ b=s.right) ∨ (a=s.right ∧ b=s.left))
    (many : 2≤(externalLabels G C s.top a).card) (emptyB : externalLabels G C s.top b=∅)
    (one : s.ArmSingle a) : Positive G C := by
  classical
  obtain ⟨data⟩ := group_data s
  obtain ⟨core⟩ := original_central_batches s data a b sides
  let T := externalLabels G C s.top a
  let A := leaves n C a
  let Y (i : T) := leaves n C i.val
  let k := fun i : T => (A∩Y i).card
  let p := fun i : T => (Y i \ A).card
  let h := fun i : T => (data.own i.val).card
  let idx := fun i : T => shareIndex A (Y i)
  let Z := fun i : T => indexedLeaf n C (Y i \ A)
  have shape : s.group=insert s.top T := by
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [group,L,R,T,emptyB]
  have membership (i : T) : i.val∈(centreless G C).erase s.top := (Finset.mem_filter.mp i.property).1
  have top (i : T) : i.val∈tops G C := (Finset.mem_filter.mp (Finset.mem_erase.mp (membership i)).2).1
  have da : a∈junk G C := sides.elim (fun h => by simpa [h.1] using s.leftDirty)
    (fun h => by simpa [h.1] using s.rightDirty)
  have db : b∈junk G C := sides.elim (fun h => by simpa [h.2] using s.rightDirty)
    (fun h => by simpa [h.2] using s.leftDirty)
  have ex (i : T) := original_external_batch s data (t := i.val) (by simp [shape,i.property])
    (Finset.mem_erase.mp (membership i)).1 A
  choose E edgeLabel using ex
  have pc (i : T) : 0<p i := Finset.card_pos.mpr (external_private_leaf s.least.1 da (top i))
  have kc (i : T) : 2≤k i := by
    obtain ⟨g,ga,gt⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp i.property).2
    exact shared_leaf_balance s.least.1 ga (Finset.mem_of_mem_erase gt)
  have idxeq (i : T) (c : Fin (k i)) :
      (A.equivFin.symm (idx i c)).val = ((A∩Y i).equivFin.symm c).val := by simp [idx,shareIndex]
  have unique : Function.Injective (fun pair : Σ i : T, Fin (k i) => idx pair.1 pair.2) := by
    rintro ⟨i,c⟩ ⟨j,d⟩ eq
    change idx i c = idx j d at eq
    have pins : ((A∩Y i).equivFin.symm c).val=((A∩Y j).equivFin.symm d).val := by
      rw [← idxeq,← idxeq,eq]
    let z := ((A∩Y i).equivFin.symm c).val.1
    have hi := Finset.mem_inter.mp ((A∩Y i).equivFin.symm c).property
    have hj := Finset.mem_inter.mp ((A∩Y j).equivFin.symm d).property
    have ga : z∈andRegion n C a := (region_pin_mem s.least.1 hi.1).1
    have gi : z∈andRegion n C i.val := (region_pin_mem s.least.1 hi.2).1
    have gj : z∈andRegion n C j.val := by
      change ((A∩Y i).equivFin.symm c).val.1 ∈ _
      rw [pins]
      exact (region_pin_mem s.least.1 hj.2).1
    have dirty := dirty_region_sub s.least.1 s.form da ga
    have neq (q : T) : z ≠ q.val := by
      intro he
      exact ((S4183.junk_iff G C _).mp dirty).2.2 (he ▸ (Finset.mem_filter.mp (top q)).2.2)
    have member (q : T) (gq : z∈andRegion n C q.val) : q.val∈s.exteriorOn z :=
      Finset.mem_filter.mpr ⟨membership q, Finset.mem_erase.mpr ⟨neq q,gq⟩⟩
    have ij : i=j := Subtype.ext (Finset.card_le_one.mp (one z ga) _ (member i gi) _ (member j gj))
    subst j
    have cd : c=d := (A∩Y i).equivFin.symm.injective (Subtype.ext pins)
    subst d; rfl
  obtain ⟨x,bal⟩ := physical_slot_balance k idx unique
  have bc : 2≤(leaves n C b).card := by
    have info := (S4183.junk_iff G C b).mp db
    apply Triangle.two_boundary _ ⟨b,root_mem_region info.1 info.2.1⟩
    intro j hj u
    exact s.least.1.2.1 j (in_region.mp hj).1 _ (Triangle.opnd_mem_for_region s.least.1 (in_region.mp hj).1 u)
  have excl {F K : Finset (Sym2 (Fin n))} {f : Fin F.card → Bool → Fin n} {g : Fin K.card → Bool → Fin n}
      (hf : ∀ i, (F.equivFin.symm i).val=s(f i false,f i true))
      (hg : ∀ i, (K.equivFin.symm i).val=s(g i false,g i true)) (apart : Disjoint F K) :
      ∀ i j c d, s(f i c,f i (!c)) ≠ s(g j d,g j (!d)) :=
    fun i j c d eq => Finset.disjoint_left.mp apart (oriented_mem hf i c) (eq ▸ oriented_mem hg j d)
  have de (i : T) : Disjoint (data.own s.top) (data.own i.val) := data.distinct s.centrelessTop
    (Finset.mem_of_mem_erase (membership i)) (Finset.mem_erase.mp (membership i)).1.symm
  have leftSub : core.le ⊆ data.own s.top := core.union ▸ Finset.subset_union_left
  have rightSub : core.ri ⊆ data.own s.top := core.union ▸ Finset.subset_union_right
  have pay := physical_star_charge k p h (by simpa [T] using many) bal bc core.guard kc pc s.four
    (indexedLeaf n C A) (indexedLeaf n C (leaves n C b)) (indexedLeaf n C ((leaves n C s.top).erase core.pin))
    idx Z core.lp core.rp E (excl core.llab core.rlab core.dis)
    (fun i => excl core.llab (edgeLabel i) ((de i).mono_left leftSub))
    (fun i => excl core.rlab (edgeLabel i) ((de i).mono_left rightSub))
    (fun i j ne => excl (edgeLabel i) (edgeLabel j) (data.distinct (Finset.mem_of_mem_erase (membership i))
      (Finset.mem_of_mem_erase (membership j)) (fun e => ne (Subtype.ext e))))
  rw [star_price_original k p bal] at pay
  have price := star_price s a b sides one emptyB core.pin core.used
  have cost : 2*core.le.card+2*core.ri.card+∑ i∈T,2*(data.own i).card ≤
        (leaves n C a).card+(leaves n C b).card+((leaves n C s.top).erase core.pin).card+
        ∑ i∈T,((leaves n C i \ leaves n C a).card+1) := by
    change 2*core.le.card+2*core.ri.card+(∑ i : T,2*(data.own i.val).card) ≤
      (leaves n C a).card+(leaves n C b).card+((leaves n C s.top).erase core.pin).card+
      ∑ i : T, ((leaves n C i.val \ leaves n C a).card+1) at pay
    rw [Finset.sum_coe_sort T (fun i => 2*(data.own i).card),
      Finset.sum_coe_sort T (fun i => (leaves n C i \ leaves n C a).card+1)] at pay
    exact pay
  have groupBound := Finset.card_biUnion_le (s := s.group) (t := data.own)
  have nm : s.top∉T := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  have sumGroup : (∑ i ∈ s.group,(data.own i).card) = (data.own s.top).card + ∑ i∈T,(data.own i).card := by
    rw [shape,Finset.sum_insert nm]
  rw [sumGroup] at groupBound
  rw [← Finset.mul_sum] at cost
  have count := core.counts
  apply finishGroupAmple s data
  apply le_trans _ price
  apply le_trans _ cost
  rw [← Nat.mul_add,← Nat.mul_add, count]
  exact Nat.mul_le_mul_left 2 groupBound

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
