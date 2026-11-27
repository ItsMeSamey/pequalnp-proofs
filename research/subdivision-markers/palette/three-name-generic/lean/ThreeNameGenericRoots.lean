import ThreeNameGenericPositive
import ThreeNameGenericTrail

namespace ThreeNameGenericRoots
open ThreeNamePacked ThreeNameGenericTrail ThreeNameGenericPositive ThreeNameSplitCircuit
open scoped BigOperators

variable {J : Type} [DecidableEq J] {w : Nat}

/-- The eight values of the named span and at most eight subsets of the three root labels. -/
def initialCheck (p : Frame J w) (i j k : J) (target a b : BitVec w)
    (table : ThreeNamePackedPins.Table w) : Bool :=
  let R : Finset J := {i,j,k}
  let nm := (ThreeNamePackedPins.asLinear table).comp (named target a b)
  decide (i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ R ⊆ p.ground ∧
    (∀ P ∈ R.powerset, P.Nonempty → (∑ e ∈ P,p.carrier.col e) ≠ 0) ∧
    nm (0,1) = ∑ e ∈ R,p.carrier.col e ∧
    ∀ P ∈ R.powerset, ∃ z : Tags, ∃ y : F, nm (z,y) = ∑ e ∈ P,p.carrier.col e)

theorem rootFacts (p : Frame J w) (i j k : J) (target a b : BitVec w)
    (table : ThreeNamePackedPins.Table w)
    (ok : initialCheck p i j k target a b table = true) :
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ({i,j,k} : Finset J) ⊆ p.ground ∧
    Independent p.carrier.col ({i,j,k} : Finset J) ∧
    ((ThreeNamePackedPins.asLinear table).comp (named target a b)) (0,1) =
      (∑ e ∈ ({i,j,k} : Finset J),p.carrier.col e) ∧
    ∀ P ⊆ ({i,j,k} : Finset J), ∃ z : Tags, ∃ y : F,
      ((ThreeNamePackedPins.asLinear table).comp (named target a b)) (z,y) =
      ∑ e ∈ P,p.carrier.col e := by
  unfold initialCheck at ok
  obtain ⟨hij,hik,hjk,ground,indep,axis,allMasks⟩ := of_decide_eq_true ok
  exact ⟨hij,hik,hjk,ground,fun P sub => indep P (Finset.mem_powerset.mpr sub),
    axis,fun P sub => allMasks P (Finset.mem_powerset.mpr sub)⟩

#print axioms rootFacts
end ThreeNameGenericRoots
