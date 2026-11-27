import ExactPlaneGaussian
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Abel
import Batteries.Tactic.OpenPrivate
namespace ExactPlaneIntersectionKernel
open ExactPlaneGaussian Submodule
open private decode_single from ExactPlaneGaussian
variable {d m : ℕ} {I : Type*}

def reduceMap (s : Bank d I) : Row d I →ₗ[F] Row d I where
  toFun := reduce s
  map_add' x y := by
    induction s generalizing x y with
    | nil => rfl
    | cons a s ih =>
      change reduce s (clear a.1 a.2 (x+y))=_
      rw [show clear a.1 a.2 (x+y)=clear a.1 a.2 x+clear a.1 a.2 y by
        simp [clear,add_smul] <;> abel]
      exact ih _ _
  map_smul' z x := by
    induction s generalizing x with
    | nil => rfl
    | cons a s ih =>
      change reduce s (clear a.1 a.2 (z • x))=_
      rw [show clear a.1 a.2 (z • x)=z • clear a.1 a.2 x by simp [clear,smul_add,smul_smul]]
      exact ih _

def masks (s : Bank m (Fin d)) : V m →ₗ[F] V d :=
  (LinearMap.snd F _ _).comp ((reduceMap s).comp (LinearMap.inl F _ _))

def generators (H : V d →ₗ[F] V m) (i : Fin d) : V d :=
  let v := fun j : Fin d => H (Pi.single j 1)
  let s := build v (List.finRange d)
  Pi.single i 1 - masks s (v i)

theorem span_generators (H : V d →ₗ[F] V m) :
    span F (Set.range (generators H)) = LinearMap.ker H := by
  classical
  let e : Fin d → V d := fun j => Pi.single j 1
  let v := fun i => H (e i)
  let s := build v (List.finRange d)
  let P := LinearMap.id (R:=F) (M:=V d) - (masks s).comp H
  have gen (i : Fin d) : generators H i=P (e i) := rfl
  have dec : decode v=H := by
    apply (Pi.basisFun F (Fin d)).ext
    intro i
    rw [Pi.basisFun_apply,decode_single]
  have mem (i : Fin d) : H (generators H i)=0 := by
    have inSpan : v i ∈ span F (v '' ((List.finRange d).toFinset : Set (Fin d))) :=
      subset_span ⟨i,by simp,rfl⟩
    obtain ⟨a,ha⟩ := (solve_hits _ _ _).mpr inSpan
    obtain ⟨val,_⟩ := solve_witness _ _ _ _ ha
    have ma : masks s (v i)=a := by
      change (if (reduce s (v i,0)).1=0 then some (reduce s (v i,0)).2 else none)=some a at ha
      split at ha
      · exact Option.some.inj ha
      · contradiction
    rw [dec] at val
    change H (e i-masks s (v i))=0
    rw [map_sub,ma,val,sub_self]
  apply le_antisymm
  · exact span_le.mpr (fun y ⟨i,hi⟩ => hi ▸ mem i)
  · intro x hx
    have fixed : P x=x := by
      change x-masks s (H x)=x
      rw [show H x=0 from hx,map_zero,sub_zero]
    rw [←fixed,←(Pi.basisFun F (Fin d)).sum_repr x,map_sum]
    apply (span F (Set.range (generators H))).sum_mem
    intro j _
    rw [map_smul]
    apply Submodule.smul_mem
    exact subset_span ⟨j,by simpa only [Pi.basisFun_apply,e] using gen j⟩

#print axioms span_generators
end ExactPlaneIntersectionKernel
