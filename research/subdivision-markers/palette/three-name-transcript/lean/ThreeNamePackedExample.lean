import ThreeNamePackedTerminal
import ThreeNamePackedPins
namespace ThreeNamePackedExample
open ThreeNamePacked ThreeNameChain ThreeNameSplitCircuit
open scoped BigOperators
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
abbrev Raw := Fin 9
def orig (i : Raw) : BitVec 7 := ([3, 7, 5, 19, 20, 27, 32, 39, 64] : List (BitVec 7)).getD i.val 0
def pinTable : ThreeNamePackedPins.Table 7 := [(1,3)]
def pivotSource (_ : Fin 7) : List Raw := [0]
theorem pinOK : ThreeNamePackedPins.check orig [0] pinTable pivotSource = true := by decide
def rawSite (i : Fin 8) : Raw := ⟨i.val+1,by have := i.isLt; omega⟩
theorem optional_word_replay : ∀ j, ThreeNamePackedPins.run pinTable (orig (rawSite j)) = words (originalLabel j) := by decide
theorem six_name_replay : ([7, 11, 13, 12, 6, 10] : List (BitVec 7)).map (ThreeNamePackedPins.run pinTable) =
    [words 0,words 1,words 2,words 3,words 4,words 5] := by decide
theorem target_replay : ThreeNamePackedPins.run pinTable (1 : BitVec 7) = words 0 ^^^ words 1 ^^^ words 2 := by decide
theorem all_original_selections (name : ((Fin 2 → ZMod 2) × ZMod 2) →ₗ[ZMod 2] Vec 7) (R : Finset Raw) :
    ThreeNamePinReduction.Exact (fun i => decode (ThreeNamePackedPins.run pinTable (orig i)))
      ((ThreeNamePackedPins.asLinear pinTable).comp name) R ↔
    ThreeNamePinReduction.Exact (fun i => decode (orig i)) name (([0] : List Raw).toFinset ∪ R) :=
  ThreeNamePackedPins.checked_lift_iff orig [0] pinTable pivotSource pinOK name R
#print axioms all_original_selections
open ThreeNamePinReduction

/-- A member of an indexed binary span is the XOR of one subset of the original labels. -/
theorem subset_sum {J : Type} [Fintype J] [DecidableEq J] {w : Nat}
    (col : J → Vec w) (A : Finset J) (y : Vec w) (h : y ∈ indexedSpan col A) :
    ∃ S ⊆ A, (∑ i ∈ S, col i) = y := by
  classical
  obtain ⟨mask,hit⟩ := (ExactPlaneGaussian.solve_hits A.toList col y).mpr (by
    simpa [indexedSpan] using h)
  obtain ⟨val,out⟩ := ExactPlaneGaussian.solve_witness A.toList col y mask hit
  refine ⟨A.filter (fun i => mask i = 1),Finset.filter_subset _ _,?_⟩
  have dec : (∑ i, mask i • col i) = y := by
    simpa [ExactPlaneGaussian.decode,LinearMap.sum_apply] using val
  rw [← dec,Finset.sum_filter]
  calc
    _ = ∑ i ∈ A, mask i • col i := by
      apply Finset.sum_congr rfl
      intro i _
      rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (mask i) with h|h <;> simp [h]
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
      intro i _ notin
      have zero := out i (by simpa using notin)
      simp [zero])

abbrev B := Fin 2 → ZMod 2
def nm : (B × ZMod 2) →ₗ[ZMod 2] Vec 7 :=
  (LinearMap.snd (ZMod 2) B (ZMod 2)).smulRight (decode (1 : BitVec 7)) +
  ((LinearMap.proj (0 : Fin 2)).comp (LinearMap.fst (ZMod 2) B (ZMod 2))).smulRight (decode (7 : BitVec 7)) +
  ((LinearMap.proj (1 : Fin 2)).comp (LinearMap.fst (ZMod 2) B (ZMod 2))).smulRight (decode (11 : BitVec 7))
def qnm := (ThreeNamePackedPins.asLinear pinTable).comp nm
def qcol (i : Raw) := decode (ThreeNamePackedPins.run pinTable (orig i))
def rawLabel (i : Raw) : I := ⟨5+i.val,by have := i.isLt; omega⟩
theorem label_data : ∀ j : Raw, j ≠ 0 → rawLabel j ∈ g0 ∧ rawLabel j ∉ roots ∧
    p0.col (rawLabel j) = qcol j := by decide
def rootCoord (a b c : Bool) : B × ZMod 2 :=
  (fun j => if (if j.val=0 then a ^^ c else b ^^ c) then 1 else 0, if c then 1 else 0)

theorem qzero_word : qcol 0 = 0 := by
  change decode (ThreeNamePackedPins.run pinTable (orig 0)) = 0
  rw [show ThreeNamePackedPins.run pinTable (orig 0) = 0 by decide, decode_zero]

theorem named_target : qnm (0,1) = ∑ i ∈ roots,p0.col i := by
  rw [root_mask_sum roots (fun _ h => h)]
  have h0 : (0:I) ∈ roots := by decide
  have h1 : (1:I) ∈ roots := by decide
  have h2 : (2:I) ∈ roots := by decide
  simp only [h0,h1,h2,decide_true]
  funext j
  exact (show ∀ j, qnm (0,1) j = decode (rootMaskWord true true true) j by decide) j

theorem coord_value : ∀ a b c : Bool, ∀ j, qnm (rootCoord a b c) j = decode (rootMaskWord a b c) j := by decide

/-- No original support containing pin 0 realizes the requested named line. -/
theorem raw_pinned_no (A : Finset Raw) (pin : 0 ∈ A) :
    ¬ Exact (fun i => decode (orig i)) nm A := by
  classical
  intro hx
  have un : ([0] : List Raw).toFinset ∪ A = A := by simpa using Finset.insert_eq_of_mem pin
  have qr : Exact qcol qnm A := (all_original_selections nm A).mpr (un.symm ▸ hx)
  let T := (A.erase 0).image rawLabel
  have atom {j} (hj : j ∈ A.erase 0) := label_data j (Finset.mem_erase.mp hj).1
  have gg : T ⊆ g0 := by
    rintro _ h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact (atom hj).1
  have dis : Disjoint roots T := Finset.disjoint_left.mpr (by
    intro i hi hm
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
    exact (atom hj).2.1 hi)
  have spans : indexedSpan p0.col T = indexedSpan qcol A := by
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · rintro _ ⟨i,hi,rfl⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      rw [(atom hj).2.2]
      exact Submodule.subset_span ⟨j,(Finset.mem_erase.mp hj).2,rfl⟩
    · rintro _ ⟨j,hj,rfl⟩
      by_cases h : j = 0
      · subst j
        rw [qzero_word]
        exact Submodule.zero_mem _
      · have inside := Finset.mem_erase.mpr ⟨h,hj⟩
        rw [← (atom inside).2.2]
        exact Submodule.subset_span ⟨rawLabel j,Finset.mem_image_of_mem _ inside,rfl⟩
  have qx : Exact p0.col qnm T := by
    intro z y
    rw [spans]
    exact qr z y
  have target := named_target
  obtain ⟨S,st,sm⟩ := subset_sum p0.col T _ ((qx 0 1).mpr rfl)
  apply noPhysical S (st.trans gg) (Finset.disjoint_left.mpr (fun _ hr hs => Finset.disjoint_left.mp dis hr (st hs))) (sm.trans target)
  intro Q hq P hp eq
  let a := decide ((0:I) ∈ P)
  let b := decide ((1:I) ∈ P)
  let c := decide ((2:I) ∈ P)
  let point := rootCoord a b c
  have hm : qnm point = ∑ i ∈ P,p0.col i :=
    (funext (coord_value a b c)).trans (root_mask_sum P hp).symm
  have belongs : (∑ i ∈ Q,p0.col i) ∈ indexedSpan p0.col T :=
    Submodule.sum_mem _ (fun i hi => Submodule.subset_span ⟨i,st (hq hi),rfl⟩)
  have namedmem : qnm point ∈ indexedSpan p0.col T := by
    rw [hm,← eq]
    exact belongs
  have z := (qx point.1 point.2).mp namedmem
  have pair : point = (0,point.2) := Prod.ext z rfl
  have bits : point.2 = 0 ∨ point.2 = 1 := (show ∀ x : ZMod 2,x=0 ∨ x=1 by decide) _
  rw [← hm,pair]
  rcases bits with zero|one
  · left
    rw [zero]
    exact qnm.map_zero
  · right
    rwa [one]

#print axioms raw_pinned_no

end ThreeNamePackedExample
