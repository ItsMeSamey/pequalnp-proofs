import DDIndexedUnaffected
import DDIndexedRoots
import DDGraphSplit
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
private theorem list_or_iff {n : ℕ} (fs : List (Signal n)) (hd : Signal n) (x : Fin n → Bool) :
    fs.foldl (join false) hd x = true ↔ hd x = true ∨ ∃ f ∈ fs, f x = true := by
  induction fs generalizing hd with
  | nil => simp
  | cons f fs ih =>
    rw [List.foldl_cons,ih]
    simp only [join,Bool.false_eq_true,if_false,Bool.or_eq_true_iff,List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨g,hg,h⟩)
      · exact .inl h
      · exact .inr ⟨f,.inl rfl,h⟩
      · exact .inr ⟨g,.inr hg,h⟩
    · rintro (h | ⟨g,rfl | hg,h⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr ⟨g,hg,h⟩

private theorem cap_old {n k u : ℕ} {C : Circuit} {p : Cuts} (ao : IsAO2 n C)
    (hk : k ≤ C.size) (hu : u<n+k) {o : Origin} {i : ℕ} {f : Signal n}
    (refeq : ref (build n C p k) u = some (o,i))
    (slot : physicalSlot n C p k u = some f) (x : Fin n → Bool) :
    W n (actualC n C p k) x i = f x := by
  have h := slot_value C p ao hk x k le_rfl u hu
  rw [refeq,slot] at h
  exact h

theorem cap_cover {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (z : SplitData G C m)
    (a b w : Fin (n+rank n C (splitCuts n C (orT G C) m) C.size)) (oa ob ow : Origin)
    (ha : ref (build n C (splitCuts n C (orT G C) m) C.size) (n+z.a) = some (oa,a.val))
    (hb : ref (build n C (splitCuts n C (orT G C) m) C.size) (n+z.b) = some (ob,b.val))
    (hw : ref (build n C (splitCuts n C (orT G C) m) C.size) (n+z.t) = some (ow,w.val))
    (x : Fin n → Bool) :
    let p := splitCuts n C (orT G C) m
    let E := (tops G C).erase z.t
    graphFun G ∅ x = true ↔ ∃ j ∈ rootIndices n C p E, gateVal n (capPrefix n C p C.size a b w) j x = true := by
  let p := splitCuts n C (orT G C) m
  let E := (tops G C).erase z.t
  let K := rank n C p C.size
  let D := capPrefix n C p C.size a b w
  have spec := cap_prefix_spec C p least.1 (k:=C.size) le_rfl a b w
  have width (j) (hj : j ∈ Finset.range C.size) : n+j<n+C.size := by have := Finset.mem_range.mp hj;omega
  have oldA := cap_old least.1 le_rfl (width _ (Finset.mem_filter.mp z.aJunk).1) ha z.leftSlot x
  have oldB := cap_old least.1 le_rfl (width _ (Finset.mem_filter.mp z.bJunk).1) hb z.rightSlot x
  have oldW := cap_old least.1 le_rfl (width _ (Finset.mem_filter.mp z.top).1) hw z.guardSlot x
  have ap : gateVal n D K x = (gateVal n C z.a x && z.w x) :=
    (spec.2.2.2.1 x).trans (congrArg₂ Bool.and oldA oldW)
  have bp : gateVal n D (K+1) x = (gateVal n C z.b x && z.w x) := by
    have h := (spec.2.2.2.2 x).trans (congrArg₂ Bool.and oldB oldW)
    change W n D x (n+(K+1)) = _
    simpa only [Nat.add_assoc] using h
  have ext (j) (hj : j ∈ E) : gateVal n D (rank n C p j) x = gateVal n C j x := by
    obtain ⟨ne,top⟩ := Finset.mem_erase.mp hj
    have off := fun h => ne (z.onlyAffected j top h)
    obtain ⟨g,hg⟩ := external_paid edge least form top off
    have jlt : j < C.size := Finset.mem_range.mp (Finset.mem_filter.mp top).1
    have tag := paid_ref C p hg jlt
    have sv := unchanged_top_slot d edge least form top off
    have orig := cap_old least.1 le_rfl (by omega) tag sv x
    let u : Fin (n+K) := ⟨n+rank n C p j,by have := paid_strict C p hg jlt; dsimp [K];omega⟩
    exact (spec.2.2.1 u x).trans orig
  have agg := congrFun (z.agree.trans least.2.1) x
  change graphFun G ∅ x = true ↔ ∃ j ∈ rootIndices n C p E, gateVal n D j x = true
  rw [←agg,list_or_iff,z.other_eq]
  simp only [rootIndices,Finset.mem_insert,Finset.mem_image,List.mem_map,Finset.mem_toList]
  change ((gateVal n C z.a x || gateVal n C z.b x) && z.w x) = true ∨ _ ↔ _
  constructor
  · rintro (h | ⟨f,⟨j,hj,rfl⟩,hf⟩)
    · rw [Bool.and_eq_true] at h
      rcases h with ⟨hab,hg⟩
      rcases Bool.or_eq_true_iff.mp hab with h | h
      · exact ⟨K,.inl rfl,by simp [ap,h,hg]⟩
      · exact ⟨K+1,.inr (.inl rfl),by simp [bp,h,hg]⟩
    · exact ⟨_,.inr (.inr ⟨j,hj,rfl⟩),(ext j hj).trans hf⟩
  · rintro ⟨j,eq | eq | ⟨i,hi,eq⟩,hj⟩
    · subst j; rw [ap,Bool.and_eq_true] at hj
      exact .inl (by simp [hj.1,hj.2])
    · subst j; rw [bp,Bool.and_eq_true] at hj
      exact .inl (by simp [hj.1,hj.2])
    · subst j; exact .inr ⟨_,⟨i,hi,rfl⟩,(ext i hi).symm.trans hj⟩
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
