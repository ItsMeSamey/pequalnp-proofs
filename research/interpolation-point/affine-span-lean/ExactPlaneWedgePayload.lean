import ExactPlaneWedgeLayout
import ExactPlaneWedgeSplit
import Batteries.Tactic.OpenPrivate
namespace ExactPlaneWedgePayload
open ExactPlaneWedgeProduct ExactPlaneWedgeLayout ExactPlaneWedgeSplit
open private mask_union from ExactPlaneWedgeSplit
abbrev Payload (n : ℕ) := Finset (Fin n) × Finset (Fin n)
def feature (a : Payload n) := actual (mask a.1) (mask a.2)
def leaf (i : Fin n) (u v : Bool) : Payload n :=
  (if u then {i} else ∅,if v then {i} else ∅)
def join (a b : Payload n) : Payload n := (a.1∪b.1,a.2∪b.2)
def packed (a : Payload n) := store n (feature a)
theorem join_feature (a b : Payload n) (u : Disjoint a.1 b.1) (v : Disjoint a.2 b.2) :
    feature (join a b) = bilinear n (feature a) (feature b) := by
  rw [feature,feature,feature,actual_join]
  simp [join,mask_union u,mask_union v]
theorem join_packed (a b : Payload n) (u : Disjoint a.1 b.1) (v : Disjoint a.2 b.2) :
    packed (join a b) = store n (bilinear n (feature a) (feature b)) :=
  congrArg (store n) (join_feature a b u v)
theorem leaf_both (i : Fin n) : leaf i true true = ({i},{i}) := rfl
#print axioms join_packed
end ExactPlaneWedgePayload
