import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-! Incidence counting on the live output cone. Operand slots, including repeated
operands, are individual occurrences. Vertex liveness enters only via positivity
away from the output and the absence of a consumer of the output. -/

namespace ScalarFork.LiveIncidence

open scoped BigOperators

inductive GatePins (V : Type*) where
  | binary (left right : V)
  | unary (arg : V)

variable {V : Type*}

def pins : List (GatePins V) → List V
  | [] => []
  | .binary a b :: gs => a :: b :: pins gs
  | .unary a :: gs => a :: pins gs

def binaryCount : List (GatePins V) → Nat
  | [] => 0
  | .binary _ _ :: gs => binaryCount gs + 1
  | .unary _ :: gs => binaryCount gs

theorem pins_length (gs : List (GatePins V)) :
    (pins gs).length = gs.length + binaryCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp only [pins, binaryCount, List.length_cons] <;> omega

def degree [DecidableEq V] (v : V) : List V → Nat
  | [] => 0
  | a :: ps => (if v = a then 1 else 0) + degree v ps

theorem sum_degree [Fintype V] [DecidableEq V] (ps : List V) :
    (∑ v : V, degree v ps) = ps.length := by
  induction ps with
  | nil => simp [degree]
  | cons a ps ih =>
    simp [degree, Finset.sum_add_distrib, ih, Nat.add_comm]

def nonoutput [Fintype V] [DecidableEq V] (out : V) : Finset V :=
  Finset.univ.erase out

def excess [Fintype V] [DecidableEq V] (out : V) (ps : List V) : Nat :=
  ∑ v ∈ nonoutput out, (degree v ps - 1)

def forks [Fintype V] [DecidableEq V] (out : V) (ps : List V) : Finset V :=
  (nonoutput out).filter (fun v => 2 ≤ degree v ps)

theorem incidence_identity [Fintype V] [DecidableEq V]
    (gs : List (GatePins V)) (out : V) (inputs : Nat)
    (hvertices : Fintype.card V = inputs + gs.length)
    (hout : degree out (pins gs) = 0)
    (hlive : ∀ v, v ≠ out → 1 ≤ degree v (pins gs)) :
    inputs + excess out (pins gs) = binaryCount gs + 1 := by
  let W := nonoutput out
  have hcard : W.card + 1 = Fintype.card V := by
    simpa [W, nonoutput] using Finset.card_erase_add_one (Finset.mem_univ out)
  have hsum : (∑ v ∈ W, degree v (pins gs)) = (pins gs).length := by
    calc
      _ = (∑ v ∈ W, degree v (pins gs)) + degree out (pins gs) := by rw [hout, Nat.add_zero]
      _ = ∑ v : V, degree v (pins gs) :=
        Finset.sum_erase_add Finset.univ (fun v => degree v (pins gs)) (Finset.mem_univ out)
      _ = _ := sum_degree _
  have split : (∑ v ∈ W, degree v (pins gs)) = W.card + excess out (pins gs) := by
    calc
      _ = ∑ v ∈ W, (1 + (degree v (pins gs) - 1)) := by
        apply Finset.sum_congr rfl
        intro v hv
        have ne : v ≠ out := (Finset.mem_erase.mp hv).1
        have := hlive v ne
        omega
      _ = _ := by simp [Finset.sum_add_distrib, excess, W]
  have hlen := pins_length gs
  omega

theorem forks_le_excess [Fintype V] [DecidableEq V] (out : V) (ps : List V) :
    (forks out ps).card ≤ excess out ps := by
  unfold forks excess
  have hb : (∑ v ∈ nonoutput out, (if 2 ≤ degree v ps then 1 else 0 : Nat)) =
      ((nonoutput out).filter (fun v => 2 ≤ degree v ps)).card := by
    simpa only [Nat.cast_id] using Finset.sum_boole (R := Nat) (fun v => 2 ≤ degree v ps) (nonoutput out)
  rw [← hb]
  apply Finset.sum_le_sum
  intro v _
  split_ifs <;> omega

/-- Any set of occupied first forks may contain many source owners per fork. -/
theorem occupied_capacity [Fintype V] [DecidableEq V]
    (gs : List (GatePins V)) (out : V) (inputs : Nat) (occupied : Finset V)
    (hvertices : Fintype.card V = inputs + gs.length)
    (hout : degree out (pins gs) = 0)
    (hlive : ∀ v, v ≠ out → 1 ≤ degree v (pins gs))
    (hoccupied : occupied ⊆ forks out (pins gs)) :
    inputs + occupied.card ≤ binaryCount gs + 1 := by
  exact (Nat.add_le_add_left
    ((Finset.card_le_card hoccupied).trans (forks_le_excess out (pins gs))) inputs).trans
    (incidence_identity gs out inputs hvertices hout hlive).le

end ScalarFork.LiveIncidence
