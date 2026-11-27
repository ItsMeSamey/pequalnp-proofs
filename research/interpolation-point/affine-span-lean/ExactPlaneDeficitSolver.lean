import ExactPlaneGeneratedWitness
import ExactPlaneComputedDeficit
namespace ExactPlaneDeficitSolver
open ExactPlaneSuppliedCoordinates ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlaneObservedSpan

def solve (p : Fin N→Key d) (b h : Fin N→Plane) :=
  ExactPlaneGeneratedDecision.run (2*(ExactPlaneComputedDeficit.computed p b+2)+1) p b h

theorem solve_iff (p : Fin N→Key d) (b h : Fin N→Plane) :
    solve p b h ≠ none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  apply ExactPlaneGeneratedDecision.decision
  rw [ExactPlaneComputedDeficit.computed_eq]

theorem witness {p : Fin N→Key d} {b h q : Fin N→Plane} {B : Finset (Fin N)}
    (found : solve p b h=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (g : Fin N→Plane) i=>g i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 :=
  ExactPlaneGeneratedDecision.returned found

def solvePacked (keys : Vector (Vector (ZMod 2) d) N) (tags heights : Vector Plane N) :=
  (solve (fun (i : Fin N) (j : Fin d)=>keys[i][j]) (fun i=>tags[i]) (fun i=>heights[i])).map
    fun ans => (Vector.ofFn ans.1,ans.2)

theorem packed_iff (keys : Vector (Vector (ZMod 2) d) N) (tags heights : Vector Plane N) :
    solvePacked keys tags heights ≠ none ↔ ∃ A : Finset (Fin N),
      ExactTrace (fun (i : Fin N) (j : Fin d)=>keys[i][j]) (fun i=>tags[i]) (fun i=>heights[i]) A := by
  unfold solvePacked
  refine Iff.trans ?_ (solve_iff (fun (i : Fin N) (j : Fin d)=>keys[i][j]) (fun i=>tags[i]) (fun i=>heights[i]))
  cases solve (fun (i : Fin N) (j : Fin d)=>keys[i][j]) (fun i=>tags[i]) (fun i=>heights[i]) <;> simp

#print axioms packed_iff
#print axioms solve_iff
#print axioms witness
end ExactPlaneDeficitSolver
