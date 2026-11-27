import ExactPlaneProfileBranch
import ExactPlaneSparseSections
import ExactPlaneComputedDeficit
namespace ExactPlaneProfileSolver
open ExactPlanePhysicalConverse ExactPlaneObservedSpan ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
open ExactPlaneSparseSections (heights actualD actualD_eq)
open ExactPlaneProfileCharts (table)
open ExactPlaneSparseANF (Form)
variable {N d r : Nat}
abbrev Selectors (d r N : Nat) := Fin r→Fin N→Form (Fin (d+d))
abbrev polynomials (s : Selectors d r N) (h : Fin N→Plane) := fun j=>ExactPlaneSparseProfile.row (heights s h j)

def rank (p : Fin N→Key d) := ExactPlaneComputedDeficit.keyRank p Finset.univ

theorem rank_eq (p : Fin N→Key d) : rank p=Module.finrank (ZMod 2) (observed p) := by
  rw [rank,ExactPlaneComputedDeficit.keyRank_eq]
  have eq : Set.range (fun i : ↥(Finset.univ : Finset (Fin N))=>p i.val)=Set.range p := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨⟨i,Finset.mem_univ _⟩,rfl⟩
  rw [eq]
  rfl

def charts (s : Selectors d r N) (p : Fin N→Key d) (h : Fin N→Plane) :=
  (ExactPlaneDegreeSampler.candidates (d+d) (2*(rank p-r+2)) (actualD s h)).map (table p)

def solve (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane) :=
  ExactPlaneEagerSelector.selectBasis (charts s p h) p b h

theorem solve_iff (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane)
    (sec : ExactPlaneProfileBranch.Sections p b h (polynomials s h)) :
    solve s p b h≠none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  classical
  unfold solve
  rw [ExactPlaneEagerSelector.selectBasis_eq]
  constructor
  · intro found
    by_contra! no
    apply found
    exact (ExactPlaneGaussianSelector.supplied_none _ _ _ _).mpr (fun q _=>no _)
  · rintro ⟨A,trace⟩ no
    obtain ⟨l,inside,good⟩ := ExactPlaneProfileBranch.sampled p b h _ sec A trace
    apply (ExactPlaneGaussianSelector.supplied_none _ _ _ _).mp no (table p l.sum) _ good
    apply List.mem_map.mpr
    refine ⟨l.sum,List.mem_map.mpr ⟨l,?_,rfl⟩,rfl⟩
    simpa only [rank_eq,actualD_eq] using inside

theorem witness {s : Selectors d r N} {p : Fin N→Key d} {b h q : Fin N→Plane}
    {B : Finset (Fin N)} (ret : solve s p b h=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (v : Fin N→Plane) i=>v i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 := by
  let cs := charts s p h
  change ExactPlaneEagerSelector.selectBasis cs p b h=some (q,B) at ret
  rw [ExactPlaneEagerSelector.selectBasis_eq] at ret
  cases hit : ExactPlaneGaussianSelector.selectCharts cs p b h with
  | none =>
    simp [ExactPlaneGaussianSelector.selectBasis,hit] at ret
  | some pair =>
    obtain ⟨v,A⟩ := pair
    obtain ⟨T,eq,sub,span,yes,count⟩ := ExactPlaneGaussianSelector.supplied_basis hit
    rw [ret] at eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj eq)
    obtain ⟨_,_,_,_,same,_⟩ := ExactPlaneGaussianSelector.first_success hit
    exact same ▸ ⟨sub,span,yes,count⟩

#print axioms solve_iff
#print axioms witness
end ExactPlaneProfileSolver
