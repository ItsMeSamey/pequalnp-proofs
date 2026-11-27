import ExactPlaneListedDecision
import ExactPlaneAcceptedSmallWitness
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.MinMax
namespace ExactPlaneExecutableSelector
open ExactPlanePhysicalConverse ExactPlaneObservedSpan ExactPlaneResidualPivots
variable {K : Type*} [AddCommGroup K] [Module F K] [DecidableEq K] {N : ℕ}

def subfamilies (A : Finset (Fin N)) : List (Finset (Fin N)) :=
  (A.sort (·≤·)).sublists.map List.toFinset

theorem mem_subfamilies (A B : Finset (Fin N)) : B∈subfamilies A ↔ B⊆A := by
  constructor
  · intro h
    obtain ⟨l,sub,rfl⟩ := List.mem_map.mp h
    intro i hi
    exact (Finset.mem_sort (·≤·)).mp ((List.mem_sublists.mp sub).subset (List.mem_toFinset.mp hi))
  · intro sub
    let l := (A.sort (·≤·)).filter (fun i=>decide (i∈B))
    have mem : l∈(A.sort (·≤·)).sublists := List.mem_sublists.mpr List.filter_sublist
    refine List.mem_map.mpr ⟨l,mem,?_⟩
    ext i
    simp only [l,List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun h=>⟨sub h,h⟩⟩

def compress (priv : Fin N→K) (tag height : Fin N→Plane) (A : Finset (Fin N)) :=
  ((subfamilies A).filter (fun B=>ExactPlaneCandidateCheck.check B priv tag height)).argmin Finset.card

theorem compress_witness (priv : Fin N→K) (tag height : Fin N→Plane) (A : Finset (Fin N))
    (hit : ExactTrace priv tag height A) :
    ∃ B,compress priv tag height A=some B ∧ B⊆A ∧ ExactTrace priv tag height B ∧
      B.card≤Module.finrank F (observed priv)+2 := by
  let choices := (subfamilies A).filter (fun B=>ExactPlaneCandidateCheck.check B priv tag height)
  have spec (B : Finset (Fin N)) : B∈choices ↔ B⊆A ∧ ExactTrace priv tag height B := by
    simp only [choices,List.mem_filter,mem_subfamilies,ExactPlaneCandidateCheck.check_iff]
  obtain ⟨small,sub,_,yes,bd⟩ := ExactPlaneAcceptedSmallWitness.physical priv tag height A hit
  have eligible := (spec small).mpr ⟨sub,yes⟩
  cases eq : choices.argmin Finset.card with
  | none =>
    have empty := List.argmin_eq_none.mp eq
    rw [empty] at eligible
    contradiction
  | some B =>
    have inMin : B∈choices.argmin Finset.card := by simp [eq]
    have found := (spec B).mp (List.argmin_mem inMin)
    exact ⟨B,eq,found.1,found.2,(List.le_of_mem_argmin eligible inMin).trans bd⟩
def runCompact (seed : List (Fin N→Plane)) (priv : Fin N→K) (tag height : Fin N→Plane) :=
  (run seed priv tag height).bind fun result =>
    (compress priv tag height result.2).map (fun subset=>(result.1,subset))

theorem runCompact_spec {seed : List (Fin N→Plane)} {priv : Fin N→K} {tag height : Fin N→Plane}
    {q : Fin N→Plane} {A : Finset (Fin N)} (found : run seed priv tag height=some (q,A)) :
    ∃ B,runCompact seed priv tag height=some (q,B) ∧ B⊆A ∧ ExactTrace priv tag height B ∧
      B.card≤Module.finrank F (observed priv)+2 := by
  obtain ⟨B,eq,sub,yes,cap⟩ := compress_witness priv tag height A (run_some found).2
  exact ⟨B,by simp [runCompact,found,eq],sub,yes,cap⟩

#print axioms runCompact_spec
#print axioms compress_witness
end ExactPlaneExecutableSelector
