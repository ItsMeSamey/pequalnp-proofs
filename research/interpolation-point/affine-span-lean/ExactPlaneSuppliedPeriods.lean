import ExactPlaneSparseTranslation
import ExactPlaneProfileSolver
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
namespace ExactPlaneSuppliedPeriods
open ExactPlaneSparseTranslation ExactPlaneAffineSubstitution ExactPlaneProfileCharts
open ExactPlaneSparseSections ExactPlaneProfileSolver ExactPlaneSuppliedCoordinates
open ExactPlaneProfileResidual
open ExactPlaneResidualPivots (Plane)
variable {d N r a : ℕ}
abbrev F := ZMod 2

def W (v : Fin a→X d) := Submodule.span F (Set.range v)
def codim (v : Fin a→X d) := (d+d)-rank v

theorem codim_eq (v : Fin a→X d) : codim v=Module.finrank F (X d ⧸ W v) := by
  rw [codim,rank_eq]
  have dim := (W v).finrank_quotient_add_finrank
  have ambient : Module.finrank F (X d)=d+d := by simp [X,ExactPlaneFieldSampler.V]
  rw [ambient] at dim
  change d+d - Module.finrank F (W v)=_
  omega

def valid (s : Selectors d r N) (h : Fin N→Plane) (v : Fin a→X d) : Bool :=
  decide (∀ i j,translate (v i) (heights s h j).1=(heights s h j).1 ∧
    translate (v i) (heights s h j).2=(heights s h j).2)

private def periodSpace (g : X d→Plane) : Submodule F (X d) where
  carrier := {u | ∀ x,g (x+u)=g x}
  zero_mem' := by simp
  add_mem' := by
    intro u w hu hw x
    rw [←add_assoc]
    exact (hw (x+u)).trans (hu x)
  smul_mem' := by
    intro c u hu x
    have bit : ∀ z:F,z=0 ∨ z=1 := by decide
    rcases bit c with rfl|rfl
    · simp
    · simpa only [one_smul] using hu x

theorem invariant {s : Selectors d r N} {h : Fin N→Plane} {v : Fin a→X d}
    (ok : valid s h v=true) (x y : X d) (diff : x-y∈W v) (j : Fin r) :
    val (polynomials s h) x j=val (polynomials s h) y j := by
  let g := fun x=>val (polynomials s h) x j
  have on : ∀ i,v i∈periodSpace g := by
    intro i z
    have pass := (of_decide_eq_true ok) i j
    exact Prod.ext ((translate_eq_iff _ _).mp pass.1 z) ((translate_eq_iff _ _).mp pass.2 z)
  have incl : W v ≤ periodSpace g := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact on i)
  have t := (show ∀ z,g (z+(x-y))=g z from incl diff) y
  have restore : y+(x-y)=x := by abel
  exact restore ▸ t

theorem valid_iff (s : Selectors d r N) (h : Fin N→Plane) (v : Fin a→X d) :
    valid s h v=true ↔ ∀ x y : X d, x-y∈W v → ∀ j,
      val (polynomials s h) x j=val (polynomials s h) y j := by
  constructor
  · exact fun ok x y diff j=>invariant ok x y diff j
  · intro eq
    apply decide_eq_true
    intro i j
    have check (x : X d) := eq (x+v i) x
      (show x+v i-x∈W v from by
        have erase : x+v i-x=v i := by abel
        rw [erase]
        exact Submodule.subset_span (Set.mem_range_self i)) j
    exact ⟨(translate_eq_iff _ _).mpr (fun x=>congrArg Prod.fst (check x)),
      (translate_eq_iff _ _).mpr (fun x=>congrArg Prod.snd (check x))⟩

#print axioms valid_iff
#print axioms invariant
#print axioms codim_eq
end ExactPlaneSuppliedPeriods
