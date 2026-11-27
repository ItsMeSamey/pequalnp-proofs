import ThreeNamePackedPins

namespace ThreeNameGenericPositive
open ThreeNamePacked ThreeNamePinReduction
abbrev F := ZMod 2
abbrev Tags := Fin 2 → F

/-- Original named line, with the two tag coordinates followed by the target bit. -/
def named {w : Nat} (target a b : BitVec w) : (Tags × F) →ₗ[F] Vec w :=
  (LinearMap.snd F Tags F).smulRight (decode target) +
  ((LinearMap.proj (0 : Fin 2)).comp (LinearMap.fst F Tags F)).smulRight (decode a) +
  ((LinearMap.proj (1 : Fin 2)).comp (LinearMap.fst F Tags F)).smulRight (decode b)

@[simp] theorem named_apply {w : Nat} (target a b : BitVec w) (z : Tags) (y : F) :
    named target a b (z,y) = y • decode target + z 0 • decode a + z 1 • decode b := rfl

def parity {w : Nat} : List (Fin w) → BitVec w → Bool
  | [], _ => false
  | j :: js, x => x.getLsbD j.val ^^ parity js x

def functional {w : Nat} : List (Fin w) → Vec w →ₗ[F] F
  | [] => 0
  | j :: js => LinearMap.proj j + functional js

def bit (b : Bool) : F := if b then 1 else 0

theorem functional_decode {w : Nat} (row : List (Fin w)) (x : BitVec w) :
    functional row (decode x) = bit (parity row x) := by
  induction row with
  | nil => rfl
  | cons j js ih =>
    change decode x j + functional js (decode x) = bit (x.getLsbD j.val ^^ parity js x)
    rw [ih]
    exact (show ∀ a b : Bool, bit a + bit b = bit (a ^^ b) by decide) _ _

def support {I : Type*} [DecidableEq I] (pins selected : List I) : Finset I :=
  (pins ++ selected).toFinset

/-- An XOR mask witnessing the target and two rows separating the forbidden
tag directions. All ID checks refer to the original input positions. -/
def check {I : Type*} [DecidableEq I] {w : Nat} (col : I → BitVec w)
    (pins selected : List I) (target a b : BitVec w) (witness : List I)
    (rowA rowB : List (Fin w)) : Bool :=
  decide (target ≠ 0) &&
  witness.all (fun i => decide (i ∈ support pins selected)) &&
  decide (xorSum (witness.map col) = target) &&
  (pins ++ selected).all (fun i => decide (parity rowA (col i) = false ∧ parity rowB (col i) = false)) &&
  decide (parity rowA a = true ∧ parity rowA b = false ∧ parity rowB a = false ∧ parity rowB b = true)

theorem xor_mem {I : Type*} [DecidableEq I] {w : Nat} (col : I → BitVec w)
    (A : Finset I) (L : List I) (inside : ∀ i ∈ L, i ∈ A) :
    decode (xorSum (L.map col)) ∈ indexedSpan (fun i => decode (col i)) A := by
  induction L with
  | nil =>
    change decode (0 : BitVec w) ∈ _
    rw [decode_zero]
    exact Submodule.zero_mem _
  | cons i L ih =>
    simp only [List.map_cons,xorSum,decode_xor]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i,inside i (List.mem_cons_self ..),rfl⟩)
      (ih (fun j hj => inside j (List.mem_cons_of_mem _ hj)))

theorem sound {I : Type*} [DecidableEq I] {w : Nat} (col : I → BitVec w)
    (pins selected : List I) (target a b : BitVec w) (witness : List I)
    (rowA rowB : List (Fin w)) (ok : check col pins selected target a b witness rowA rowB = true) :
    pins.toFinset ⊆ support pins selected ∧
    Exact (fun i => decode (col i)) (named target a b) (support pins selected) := by
  simp only [check,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨_,inside⟩,hit⟩,zero⟩,taa,tab,tba,tbb⟩ := ok
  let S := indexedSpan (fun i => decode (col i)) (support pins selected)
  have axis : decode target ∈ S := hit ▸ xor_mem col _ witness inside
  have annih (r : List (Fin w)) (h : ∀ i ∈ pins ++ selected, parity r (col i) = false) :
      S ≤ LinearMap.ker (functional r) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change functional r (decode (col i)) = 0
    rw [functional_decode,h i (List.mem_toFinset.mp hi)]
    rfl
  have kerA := annih rowA (fun i hi => (zero i hi).1)
  have kerB := annih rowB (fun i hi => (zero i hi).2)
  have targetA : functional rowA (decode target) = 0 := kerA axis
  have targetB : functional rowB (decode target) = 0 := kerB axis
  refine ⟨fun i hi => List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hi)), ?_⟩
  intro z y
  change (y • decode target + z 0 • decode a + z 1 • decode b) ∈ S ↔ z = 0
  constructor
  · intro hs
    have a0 : functional rowA (y • decode target + z 0 • decode a + z 1 • decode b) = 0 := kerA hs
    have b0 : functional rowB (y • decode target + z 0 • decode a + z 1 • decode b) = 0 := kerB hs
    simp [map_add,map_smul,targetA,functional_decode,taa,tab,bit] at a0
    simp [map_add,map_smul,targetB,functional_decode,tba,tbb,bit] at b0
    funext j
    fin_cases j
    · exact a0
    · exact b0
  · rintro rfl
    simpa using S.smul_mem y axis

theorem pins_only {I : Type*} [DecidableEq I] {w : Nat} (col : I → BitVec w)
    (pins : List I) (target a b : BitVec w) (witness : List I) (rowA rowB : List (Fin w))
    (ok : check col pins [] target a b witness rowA rowB = true) :
    Exact (fun i => decode (col i)) (named target a b) pins.toFinset := by
  simpa [support] using (sound col pins [] target a b witness rowA rowB ok).2

section Controls
private def original (i : Fin 3) : BitVec 6 := ([3,35,33] : List (BitVec 6)).getD i.val 0
example : check original [0] [1,2] 1 7 11 [0,1,2] [2] [3] = true := by decide
example : check original [0] [2] 1 7 11 [0,1,2] [2] [3] = false := by decide
example : check original [0] [1,2] 1 7 11 [0,1,2] [2] [2] = false := by decide
example : check (fun _ : Fin 1 => (1 : BitVec 3)) [0] [] 1 2 4 [0] [1] [2] = true := by decide
end Controls

#print axioms sound
#print axioms pins_only
end ThreeNameGenericPositive
