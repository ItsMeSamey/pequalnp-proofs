import ExactPlaneNumericalRows
import ExactPlaneWedgeSplit
namespace ExactPlaneWedgeCodec
open ExactPlaneWedgeProduct
open scoped BigOperators
abbrev Word (r : ℕ) := Fin r → F
structure Code (r : ℕ) where
  first : Word r
  second : Word r
  p : Word r
  q : Word r

def zero (r : ℕ) : Code r := ⟨0,0,0,0⟩
def codes (r : ℕ) : List (Code r) := do
  let a ← ExactPlaneNumericalRows.words r
  let b ← ExactPlaneNumericalRows.words r
  let p ← ExactPlaneNumericalRows.words r
  let q ← ExactPlaneNumericalRows.words r
  return ⟨a,b,p,q⟩

def image {r d : ℕ} (cols : Fin r → Word d) (x : Word r) : Word d :=
  fun j => ∑ i, x i * cols i j

def gamma {r : ℕ} (s : Code r) (x : Word r) : F × F :=
  (∑ i, x i * s.first i, ∑ i, x i * s.second i)

def compatible {a b c d : ℕ} (A : Fin a → Word d) (B : Fin b → Word d)
    (C : Fin c → Word d) (l : Code a) (r : Code b) (s : Code c) : Bool :=
  decide (image A l.p + image B r.p = image C s.p) &&
  decide (image A l.q + image B r.q = image C s.q) &&
  (ExactPlaneNumericalRows.words a).all fun x =>
    (ExactPlaneNumericalRows.words b).all fun y =>
      (ExactPlaneNumericalRows.words c).all fun z =>
        decide (image A x + image B y = image C z → gamma l x + gamma r y = gamma s z)

theorem codes_complete {r : ℕ} (s : Code r) : s ∈ codes r := by
  rcases s with ⟨a,b,p,q⟩
  simp [codes,List.mem_flatMap,ExactPlaneNumericalRows.mem_words]

end ExactPlaneWedgeCodec
