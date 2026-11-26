import ThresholdUpperPostImages
import Mathlib.Data.List.OfFn
namespace ThresholdUpperCollisionMass
open ThresholdUpperSecond ThresholdUpperInjection ThresholdUpperExtension ThresholdUpperPostImages
open Classical
abbrev Out {w} (Q : Finset (Fin w)) := {i : Fin w // i∉Q}
abbrev Fresh {w} (Q R : Finset (Fin w)) := {i : Out Q // i.val∈R}
abbrev Rest {w} (Q R : Finset (Fin w)) := {i : Out Q // i.val∉R}

noncomputable def firstSplit {w} (Q : Finset (Fin w)) : Fin w ≃ ↥Q ⊕ Out Q :=
  (Equiv.sumCompl (·∈Q)).symm
noncomputable def secondSplit {w} (Q R : Finset (Fin w)) : Out Q ≃ Fresh Q R ⊕ Rest Q R :=
  (Equiv.sumCompl (fun i : Out Q => i.val∈R)).symm

noncomputable def sites {w z} (Q R : Finset (Fin w)) (f : ↥Q ↪ Edges z) :=
  Finset.univ.biUnion (fun i : ↥Q => (f i).val) \
    (Finset.univ.filter (fun i : ↥Q => i.val∈R)).biUnion (fun i => (f i).val)

theorem eval_sites {w z} (Q R : Finset (Fin w)) (u : Injection w z) :
    sites Q R (splitInj (firstSplit Q) u).1 = terminal u Q \ terminal u (Q∩R) := by
  classical
  have first (i : ↥Q) : (splitInj (firstSplit Q) u).1 i=u i.val := rfl
  have lhs : Finset.univ.biUnion (fun i : ↥Q => ((splitInj (firstSplit Q) u).1 i).val)=terminal u Q := by
    ext v
    simp only [first,terminal,Finset.mem_biUnion,Finset.mem_univ,true_and,Subtype.exists]
    exact ⟨fun ⟨a,ha,h⟩ => ⟨a,ha,h⟩,fun ⟨a,ha,h⟩ => ⟨a,ha,h⟩⟩
  have rhs : (Finset.univ.filter (fun i : ↥Q => i.val∈R)).biUnion
      (fun i => ((splitInj (firstSplit Q) u).1 i).val)=terminal u (Q∩R) := by
    ext v
    simp [first,terminal,Finset.mem_biUnion,Subtype.exists,and_assoc,and_left_comm,and_comm]
  exact congrArg₂ (· \ ·) lhs rhs

set_option maxHeartbeats 1200000 in
/-- Named actual second box R after exposing Q. The bad partial event depends
only on the fresh images and the fixed first images. If their residual site
set has the wrong size, the collision section is empty. -/
theorem mass {w z q} (Q R : Finset (Fin w)) (q4 : Q.card=4) (r4 : R.card=4)
    (freshSize : (R \ Q).card=q) (order : Fin q ≃ Fresh Q R) :
    (Finset.univ.filter (fun u : Injection w z =>
      (terminal u Q).card=8 ∧ (terminal u R).card=8 ∧ terminal u R=terminal u Q)).card ≤
    Fintype.card (↥Q ↪ Edges z)*partitionCount q (2*q)*
      ((Fintype.card (Edges z)-Fintype.card ↥Q)-Fintype.card (Fresh Q R)).descFactorial
        (Fintype.card (Rest Q R)) := by
  classical
  let bad := fun f : ↥Q ↪ Edges z =>
    if (sites Q R f).card=2*q then allowed (X:=Fresh Q R) f (sites Q R f) else ∅
  have cap (f) : (bad f).card≤partitionCount q (2*q) := by
    dsimp [bad]
    split
    · exact allowed_card _ _ q order ‹_›
    · simp
  have total := conditional_mass (firstSplit Q) (secondSplit Q R) bad _ cap
  apply le_trans (Finset.card_le_card ?_) total
  intro u hu
  obtain ⟨q8,r8,eq⟩ := (Finset.mem_filter.mp hu).2
  let f := (splitInj (firstSplit Q) u).1
  let tail := (splitInj (firstSplit Q) u).2
  let g := (splitInj (secondSplit Q R) tail).1
  have get (x : Fresh Q R) : xy f g x=(u x.val.val).val := rfl
  obtain ⟨sz,incl,apart⟩ := ThresholdUpperEventGeometry.residual u Q R q4 r4 q8 r8 eq
  have sr : (sites Q R f).card=2*q := by
    change (sites Q R (splitInj (firstSplit Q) u).1).card=2*q
    rw [eval_sites,sz,freshSize]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change g∈bad f
  rw [show bad f=allowed f (sites Q R f) from if_pos sr]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,?_⟩
  · intro x
    rw [get,show sites Q R f=terminal u Q \ terminal u (Q∩R) from eval_sites _ _ _]
    exact incl _ (Finset.mem_sdiff.mpr ⟨x.property,x.val.property⟩)
  · intro x y ne
    rw [get,get]
    exact apart (Finset.mem_sdiff.mpr ⟨x.property,x.val.property⟩)
      (Finset.mem_sdiff.mpr ⟨y.property,y.val.property⟩) (fun h => ne (Subtype.ext (Subtype.ext h)))
theorem no_one {w z} (Q R : Finset (Fin w)) (u : Injection w z)
    (q4 : Q.card=4) (r4 : R.card=4) (one : (R \ Q).card=1)
    (q8 : (terminal u Q).card=8) (r8 : (terminal u R).card=8) (eq : terminal u R=terminal u Q) : False := by
  classical
  have a := Finset.card_sdiff_add_card_inter Q R
  have b := Finset.card_sdiff_add_card_inter R Q
  rw [Finset.inter_comm R Q] at b
  have one' : (Q \ R).card=1 := by omega
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp one
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp one'
  have xx : x∈R \ Q := by rw [hx]; simp
  have yy : y∈Q \ R := by rw [hy]; simp
  obtain ⟨sz,inside,_⟩ := ThresholdUpperEventGeometry.residual u Q R q4 r4 q8 r8 eq
  obtain ⟨_,inside',_⟩ := ThresholdUpperEventGeometry.residual u R Q r4 q4 r8 q8 eq.symm
  have i := inside x xx
  have j := inside' y yy
  rw [eq,Finset.inter_comm R Q] at j
  rw [one] at sz
  have ix := Finset.eq_of_subset_of_card_le i (by rw [sz,ThresholdUpperEventGeometry.edge_two])
  have iy := Finset.eq_of_subset_of_card_le j (by rw [sz,ThresholdUpperEventGeometry.edge_two])
  have same := u.injective (Subtype.ext (ix.trans iy.symm))
  exact (Finset.mem_sdiff.mp xx).2 (same.symm ▸ (Finset.mem_sdiff.mp yy).1)
end ThresholdUpperCollisionMass
