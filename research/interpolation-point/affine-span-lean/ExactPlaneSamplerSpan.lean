import ExactPlaneActivationSlice
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
namespace ExactPlaneSamplerSpan
open Classical
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneActivationSlice
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Every feasible pattern on at most R supplied homogeneous rows is hit.
Repeated or dependent rows are allowed; affine offsets cancel on comparing
two points with the same prescribed measurement. -/
def Hits (seed : Finset (Vec J)) (R : Nat) : Prop :=
  ∀ k≤R,∀ read : Fin k→Vec J →ₗ[F] F,∀ x : Vec J,
    ∃ s∈seed,∀ i,read i s=read i x

theorem span_slice (seed : Finset (Vec J)) (r : Nat) (hit : Hits seed (r+1))
    (k : Nat) (hk : k≤r) (read : Fin k→Vec J →ₗ[F] F) (offset target : Fin k→F) :
    (affineSpan F (slice seed read offset target:Set (Vec J)) : Set (Vec J))=
      {x | Active read offset target x} := by
  classical
  let S := slice seed read offset target
  let U := affineSpan F (S:Set (Vec J))
  ext x
  constructor
  · intro hx
    exact span_active read offset target S (fun s hs => (Finset.mem_filter.mp hs).2) hx
  · intro hx
    change Active read offset target x at hx
    change x∈U
    have active_of {s : Vec J} (same : ∀ i,read i s=read i x) : Active read offset target s :=
      fun i => by rw [same i]; exact hx i
    obtain ⟨b,bs,rb⟩ := hit k (by omega) read x
    have bS : b∈S := Finset.mem_filter.mpr ⟨bs,active_of rb⟩
    have bu : b∈U := mem_affineSpan F (show b∈(S:Set (Vec J)) from bS)
    by_contra outside
    have sep : x-b∉U.direction := fun m =>
      outside ((AffineSubspace.vsub_right_mem_direction_iff_mem bu x).mp m)
    obtain ⟨φ,neq,ann⟩ := Submodule.exists_dual_map_eq_bot_of_notMem sep inferInstance
    let test : Fin (k+1)→Vec J →ₗ[F] F := Fin.cases φ read
    obtain ⟨s,ss,same⟩ := hit (k+1) (by omega) test x
    have sr (i : Fin k) : read i s=read i x := by simpa [test] using same i.succ
    have fs : φ s=φ x := by simpa [test] using same 0
    have sS : s∈S := Finset.mem_filter.mpr ⟨ss,active_of sr⟩
    have su : s∈U := mem_affineSpan F (show s∈(S:Set (Vec J)) from sS)
    have v : s-b∈U.direction := (AffineSubspace.vsub_right_mem_direction_iff_mem bu s).mpr su
    have mem : φ (s-b)∈U.direction.map φ := ⟨s-b,v,rfl⟩
    rw [ann,Submodule.mem_bot] at mem
    exact neq (by simpa only [map_sub,fs] using mem)

/-- All affine cosets of intrinsic codimension at most r fit the row format:
quotient coordinates give exactly finrank(V/U.direction) scalar rows. -/
theorem span_coset (seed : Finset (Vec J)) (r : Nat) (hit : Hits seed (r+1))
    (A : AffineSubspace F (Vec J)) (b : Vec J) (hb : b∈A)
    (rank : Module.finrank F ((Vec J) ⧸ A.direction)≤r) :
    affineSpan F ((seed.filter (fun s => s∈A)):Set (Vec J))=A := by
  classical
  let U := A.direction
  let d := Module.finrank F ((Vec J) ⧸ U)
  let basis := Module.finBasis F ((Vec J) ⧸ U)
  let read : Fin d→Vec J →ₗ[F] F := fun i => (basis.coord i).comp U.mkQ
  let target := fun i => read i b
  have iff (x : Vec J) : Active read (fun _ => 0) target x ↔ x∈A := by
    change (∀ i,read i x+0=read i b) ↔ x∈A
    simp only [add_zero]
    rw [←AffineSubspace.vsub_right_mem_direction_iff_mem hb x]
    change _ ↔ x-b∈U
    rw [←Submodule.Quotient.mk_eq_zero,←Submodule.mkQ_apply,LinearMap.map_sub,sub_eq_zero]
    constructor
    · intro eq
      apply basis.repr.injective
      ext i
      exact eq i
    · intro eq i
      exact congrArg (basis.coord i) eq
  have eq : slice seed read (fun _ => 0) target=seed.filter (fun s => s∈A) := by
    ext s; simp [slice,iff]
  apply SetLike.coe_injective
  rw [←eq,span_slice seed r hit d rank]
  exact Set.ext iff
def HitsCosets (seed : Finset (Vec J)) (R : Nat) : Prop :=
  ∀ A : AffineSubspace F (Vec J),(A:Set (Vec J)).Nonempty →
    Module.finrank F ((Vec J) ⧸ A.direction)≤R → ∃ x∈seed,x∈A

theorem hits_of_cosets {seed : Finset (Vec J)} {r : Nat} (hit : HitsCosets seed r) :
    Hits seed r := by
  classical
  intro k hk read x
  let φ : Vec J →ₗ[F] (Fin k→F) := LinearMap.pi read
  let A := AffineSubspace.mk' x (LinearMap.ker φ)
  have based : x∈A := AffineSubspace.self_mem_mk' _ _
  have cost : Module.finrank F ((Vec J) ⧸ A.direction)≤k := by
    rw [show A.direction=LinearMap.ker φ by exact AffineSubspace.direction_mk' _ _,
      φ.quotKerEquivRange.finrank_eq]
    exact (LinearMap.range φ).finrank_le.trans_eq (Module.finrank_fin_fun F)
  obtain ⟨s,hs,sa⟩ := hit A ⟨x,based⟩ (cost.trans hk)
  have eq := AffineSubspace.mem_mk'.mp sa
  change φ (s-x)=0 at eq
  rw [map_sub,sub_eq_zero] at eq
  exact ⟨s,hs,fun i => congrFun eq i⟩

theorem transfer {seed : Finset (Vec J)} {r : Nat} (hit : HitsCosets seed (r+1))
    (A : AffineSubspace F (Vec J)) (nonempty : (A:Set (Vec J)).Nonempty)
    (rank : Module.finrank F ((Vec J) ⧸ A.direction)≤r) :
    affineSpan F ((seed.filter (fun x => x∈A)):Set (Vec J))=A := by
  obtain ⟨b,hb⟩ := nonempty
  exact span_coset seed r (hits_of_cosets hit) A b hb rank

#print axioms transfer
#print axioms span_slice
#print axioms span_coset
end ExactPlaneSamplerSpan
