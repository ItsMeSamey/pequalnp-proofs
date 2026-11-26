import GateSurplus

namespace T2PairSemantics
open PEqualNP.CircuitLowerBounds

def target (x : List Bool) : Bool := decide (2 ≤ x.count true)

def computes (C : Circuit) (n : Nat) : Prop :=
  ∀ x : List Bool, x.length = n → C.eval x = target x

/-- Insert a disabled raw, keeping the original ordering of every surviving raw. -/
def pinAt (i : Nat) (x : List Bool) : List Bool :=
  x.take i ++ false :: x.drop i

theorem pinAt_length (i : Nat) (x : List Bool) :
    (pinAt i x).length = x.length + 1 := by
  have h := congrArg List.length (List.take_append_drop i x)
  simp only [List.length_append] at h
  simp only [pinAt, List.length_append, List.length_cons]
  omega

theorem pinAt_count (i : Nat) (x : List Bool) :
    (pinAt i x).count true = x.count true := by
  have h := congrArg (List.count true) (List.take_append_drop i x)
  simp only [List.count_append] at h
  simpa [pinAt, List.count_append] using h

/-- Coordinates i,j are successive insertion positions: inserting at j
    first and i second realizes any two distinct final positions i < j+1. -/
theorem pair_transfer (C D : Circuit) (m i j : Nat)
    (rep : computes C (m+2))
    (evalMinor : ∀ x : List Bool, x.length = m →
      D.eval x = C.eval (pinAt i (pinAt j x))) : computes D m := by
  intro x hx
  rw [evalMinor x hx, rep _ (by simp [pinAt_length, hx, Nat.add_assoc])]
  simp [target, pinAt_count]

def lower (n k : Nat) : Prop :=
  ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → computes D n → k ≤ D.size

/-- A floor for the smaller arity can be applied directly to the compiled
    physical minor. The caller provides the witnessed physical savings. -/
theorem pair_cost (C D : Circuit) (m i j k savings : Nat)
    (rep : computes C (m+2))
    (evalMinor : ∀ x : List Bool, x.length = m →
      D.eval x = C.eval (pinAt i (pinAt j x)))
    (mono : PEqualNP.MetaComplexity.Monotone2 D)
    (cost : D.size + savings ≤ C.size) (floor : lower m k) :
    k + savings ≤ C.size := by
  have h := floor D mono (pair_transfer C D m i j rep evalMinor)
  omega

end T2PairSemantics
