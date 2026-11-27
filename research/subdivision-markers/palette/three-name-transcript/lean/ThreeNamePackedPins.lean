import ThreeNamePinReduction
import ThreeNamePacked

namespace ThreeNamePackedPins
open ThreeNamePacked ThreeNamePinReduction ExactPlaneGaussian
variable {w : ℕ} {I : Type*} [DecidableEq I]

abbrev Table (w : ℕ) := List (Fin w × BitVec w)

/-- The table is supplied in the exact order of the packed bit-test/XOR loop. -/
def run : Table w → BitVec w → BitVec w
  | [], x => x
  | (i,p)::s, x => run s (if x.getLsbD i.val then x ^^^ p else x)

def step (i : Fin w) (p : BitVec w) : Vec w →ₗ[F] Vec w :=
  LinearMap.id + (LinearMap.proj i).smulRight (ThreeNamePacked.decode p)

def asLinear : Table w → Vec w →ₗ[F] Vec w
  | [] => LinearMap.id
  | (i,p)::s => (asLinear s).comp (step i p)

theorem represented (s : Table w) (x : BitVec w) :
    ThreeNamePacked.decode (run s x) = asLinear s (ThreeNamePacked.decode x) := by
  induction s generalizing x with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨i,p⟩ := a
    rw [run, ih]
    change _ = asLinear s (ThreeNamePacked.decode x + (ThreeNamePacked.decode x i) • ThreeNamePacked.decode p)
    have coeff : ThreeNamePacked.decode x i = (if x.getLsbD i.val then 1 else 0) := rfl
    rw [coeff]
    cases h : x.getLsbD i.val <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, zero_smul, add_zero, one_smul, decode_xor]

/-- Root pair sums and interface sums commute with literal packed replay. -/
theorem run_xor (s : Table w) (x y : BitVec w) :
    run s (x ^^^ y) = run s x ^^^ run s y := by
  apply ThreeNamePacked.decode_injective
  rw [represented,decode_xor,map_add,decode_xor,represented,represented]

theorem run_xorSum (s : Table w) (xs : List (BitVec w)) :
    run s (xorSum xs) = xorSum (xs.map (run s)) := by
  induction xs with
  | nil =>
    apply ThreeNamePacked.decode_injective
    simp only [List.map_nil,xorSum,represented,decode_zero,map_zero]
  | cons x xs ih => simp only [List.map_cons,xorSum,run_xor,ih]

private theorem correction (s : Table w) (S : Submodule F (Vec w))
    (rows : ∀ a ∈ s, ThreeNamePacked.decode a.2 ∈ S) (x : Vec w) :
    asLinear s x - x ∈ S := by
  induction s generalizing x with
  | nil => simp [asLinear]
  | cons a s ih =>
    obtain ⟨i,p⟩ := a
    let y := step i p x
    have h₁ := ih (fun a ha => rows a (List.mem_cons_of_mem _ ha)) y
    have h₂ : y - x ∈ S := by
      change x + x i • ThreeNamePacked.decode p - x ∈ S
      simpa only [add_sub_cancel_left] using S.smul_mem (x i) (rows (i,p) (List.mem_cons_self ..))
    have sum := S.add_mem h₁ h₂
    change asLinear s y - x ∈ S
    simpa only [sub_add_sub_cancel] using sum

theorem certified_kernel (col : I → BitVec w) (pins : List I) (s : Table w)
    (rows : ∀ a ∈ s, ThreeNamePacked.decode a.2 ∈ indexedSpan (fun i => ThreeNamePacked.decode (col i)) pins.toFinset)
    (kills : ∀ i ∈ pins, run s (col i) = 0) :
    LinearMap.ker (asLinear s) = indexedSpan (fun i => ThreeNamePacked.decode (col i)) pins.toFinset := by
  let S := indexedSpan (fun i => ThreeNamePacked.decode (col i)) pins.toFinset
  apply le_antisymm
  · intro x hx
    change asLinear s x = 0 at hx
    have h := correction s S rows x
    simpa [hx] using S.neg_mem h
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change asLinear s (ThreeNamePacked.decode (col i)) = 0
    rw [← represented, kills i (List.mem_toFinset.mp hi), decode_zero]

theorem residual_eq_iff (col : I → BitVec w) (pins : List I) (s : Table w)
    (rows : ∀ a ∈ s, ThreeNamePacked.decode a.2 ∈ indexedSpan (fun i => ThreeNamePacked.decode (col i)) pins.toFinset)
    (kills : ∀ i ∈ pins, run s (col i) = 0) (x y : BitVec w) :
    run s x = run s y ↔
    project (fun i => ThreeNamePacked.decode (col i)) pins (ThreeNamePacked.decode x) =
    project (fun i => ThreeNamePacked.decode (col i)) pins (ThreeNamePacked.decode y) := by
  rw [← ThreeNamePacked.decode_injective.eq_iff, represented, represented, ← sub_eq_zero, ← map_sub,
      ← sub_eq_zero (a := project _ _ _) (b := project _ _ _), ← map_sub]
  change _ ∈ LinearMap.ker (asLinear s) ↔ _ ∈ LinearMap.ker (project _ _)
  rw [certified_kernel col pins s rows kills, kernel]

/-- Check an ordered MSB table, including an original-index XOR witness
for every pivot row. Repeated indices cancel modulo two. -/
def check (col : I → BitVec w) (pins : List I) (s : Table w)
    (support : Fin w → List I) : Bool :=
  decide (s.Pairwise (fun a b => b.1 < a.1)) &&
  s.all (fun a => decide (a.2 ≠ 0 ∧ a.2.toNat.log2 = a.1.val) && (support a.1).all (fun i => decide (i ∈ pins)) &&
    decide (xorSum ((support a.1).map col) = a.2)) &&
  pins.all (fun i => decide (run s (col i) = 0))

theorem checked_kernel (col : I → BitVec w) (pins : List I) (s : Table w)
    (support : Fin w → List I) (ok : check col pins s support = true) :
    LinearMap.ker (asLinear s) =
      indexedSpan (fun i => ThreeNamePacked.decode (col i)) pins.toFinset := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok
  apply certified_kernel col pins s _ ok.2
  intro a ha
  obtain ⟨⟨_,incl⟩, roweq⟩ := ok.1.2 a ha
  let S := indexedSpan (fun i => ThreeNamePacked.decode (col i)) pins.toFinset
  have decode_sum (L : List I) (hL : ∀ i ∈ L, i ∈ pins) :
      ThreeNamePacked.decode (xorSum (L.map col)) ∈ S := by
    induction L with
    | nil =>
      change ThreeNamePacked.decode (0 : BitVec w) ∈ S
      rw [ThreeNamePacked.decode_zero]
      exact S.zero_mem
    | cons i L ih =>
      simp only [List.map_cons, xorSum, decode_xor]
      apply S.add_mem _ (ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)))
      apply Submodule.subset_span
      exact ⟨i,List.mem_toFinset.mpr (hL i (List.mem_cons_self ..)),rfl⟩
  rw [← roweq]
  exact decode_sum _ incl

/-- Direct lift of literal replay for the selected original positions. -/
theorem checked_lift_iff {B : Type*} [AddCommGroup B] [Module F B]
    (col : I → BitVec w) (pins : List I) (s : Table w) (support : Fin w → List I)
    (ok : check col pins s support = true) (name : (B × F) →ₗ[F] Vec w) (R : Finset I) :
    Exact (fun i => ThreeNamePacked.decode (run s (col i))) ((asLinear s).comp name) R ↔
      Exact (fun i => ThreeNamePacked.decode (col i)) name (pins.toFinset ∪ R) := by
  let v := fun i => ThreeNamePacked.decode (col i)
  let q := asLinear s
  have img : indexedSpan (fun i => ThreeNamePacked.decode (run s (col i))) R =
      (indexedSpan v R).map q := by
    simp only [indexedSpan, represented, Submodule.map_span, Set.image_image, Function.comp_def, q, v]
  have un : indexedSpan v (pins.toFinset ∪ R) = indexedSpan v R ⊔ indexedSpan v pins.toFinset := by
    simp only [indexedSpan,Finset.coe_union,Set.image_union,Submodule.span_union,sup_comm]
  have transfer (x : Vec w) : asLinear s x ∈ indexedSpan (fun i => ThreeNamePacked.decode (run s (col i))) R ↔
      x ∈ indexedSpan v (pins.toFinset ∪ R) := by
    rw [img, un]
    change x ∈ ((indexedSpan v R).map q).comap q ↔ _
    rw [Submodule.comap_map_eq,checked_kernel col pins s support ok]
  constructor <;> intro h z y
  · exact (transfer _).symm.trans (h z y)
  · exact (transfer _).trans (h z y)

#print axioms checked_lift_iff
#print axioms checked_kernel
#print axioms certified_kernel
#print axioms residual_eq_iff
end ThreeNamePackedPins
