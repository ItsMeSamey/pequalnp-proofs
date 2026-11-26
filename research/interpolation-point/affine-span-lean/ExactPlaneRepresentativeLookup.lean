import ExactPlaneLookupDeterminant
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.ZMod

namespace ExactPlaneRepresentativeLookup
open ExactPlaneLookupDeterminant ExactPlaneAffineSpanHit ExactPlaneAffineSubstitution
open scoped BigOperators
open Module
variable {I K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K] [Module F K] {N : ℕ}

structure Selection (B : Basis I F K) (priv : Fin N → K) (tag : Fin N → F × F) where
  full : Finset I
  available : ∀ i ∈ full, ∀ t, ∃ e, priv e = B i ∧ tag e = t
  anchor : (i : I) → i ∉ full → Fin N
  anchor_key : ∀ i hi, priv (anchor i hi) = B i

variable {B : Basis I F K} {priv : Fin N → K} {tag : Fin N → F × F}

noncomputable def bucket (B : Basis I F K) (priv : Fin N → K) (tag : Fin N → F × F)
    (i : I) (t : F × F) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun e => priv e = B i ∧ tag e = t)

private theorem occupied (s : Selection B priv tag) (i : I) (hi : i ∈ s.full) (t : F × F) :
    (bucket B priv tag i t).Nonempty := by
  classical
  obtain ⟨e,he⟩ := s.available i hi t
  exact ⟨e,by simpa [bucket] using he⟩

noncomputable def Selection.rep (s : Selection B priv tag) (i : I) (t : F × F) : Fin N :=
  if hi : i ∈ s.full then (bucket B priv tag i t).min' (occupied s i hi t) else s.anchor i hi

theorem Selection.full_spec (s : Selection B priv tag) (i : I) (hi : i ∈ s.full) (t : F × F) :
    priv (s.rep i t) = B i ∧ tag (s.rep i t) = t := by
  classical
  simpa [Selection.rep,hi,bucket] using
    (Finset.min'_mem (bucket B priv tag i t) (occupied s i hi t))

def target (x : Vec (I × Bool)) (i : I) : F × F := (x (i,false),x (i,true))

def Selection.Eligible (s : Selection B priv tag) (x : Vec (I × Bool)) : Prop :=
  ∀ i hi, tag (s.anchor i hi) = target x i

theorem Selection.actual (s : Selection B priv tag) {x : Vec (I × Bool)} (ok : s.Eligible x) (i : I) :
    priv (s.rep i (target x i)) = B i ∧ tag (s.rep i (target x i)) = target x i := by
  by_cases h : i ∈ s.full
  · exact s.full_spec i h _
  · simpa [Selection.rep,h] using And.intro (s.anchor_key i h) (ok i h)

noncomputable def tagChart (B : Basis I F K) (x : Vec (I × Bool)) : K →ₗ[F] F × F :=
  B.constr F (target x)

noncomputable def lift (s : Selection B priv tag) (height : Fin N → F × F) (x : Vec (I × Bool)) :
    K →ₗ[F] F × F := B.constr F (fun i => height (s.rep i (target x i)))

def component : Bool → (F × F) →ₗ[F] F
  | false => LinearMap.fst F F F
  | true => LinearMap.snd F F F

private def constant {J : Type*} (v : F) : Bit J := ⟨v,fun _ => 0⟩
private def probe {J : Type*} [DecidableEq J] (j : J) : Bit J := ⟨0,fun i => if i=j then 1 else 0⟩

private theorem constant_read {J : Type*} [Fintype J] [DecidableEq J] (v : F) (x : Vec J) :
    (constant v).read x = v := by simp [constant,Bit.read]

private theorem probe_read {J : Type*} [Fintype J] [DecidableEq J] (j : J) (x : Vec J) :
    (probe j).read x = x j := by
  classical
  have binary : ∀ z : F, z = 0 ∨ z = 1 := by decide
  rcases binary (x j) with h|h <;> simp [probe,Bit.read,Finset.sum_ite_eq',support,h]

noncomputable def code (s : Selection B priv tag) (height : Fin N → F × F) (e : Fin N)
    (side : Bool) : Residual (I × Bool) I where
  base := constant (component side (height e))
  left i := probe (i,false)
  right i := probe (i,true)
  table i t := component side (height (s.rep i t))
  weight i := B.repr (priv e) i

theorem code_read (s : Selection B priv tag) (height : Fin N → F × F) (e : Fin N)
    (side : Bool) (x : Vec (I × Bool)) :
    (code s height e side).read x = component side (height e + lift s height x (priv e)) := by
  classical
  simp only [Residual.read,code,constant_read,probe_read,map_add,lift,Basis.constr_apply_fintype,
    map_sum,map_smul,smul_eq_mul,target,Basis.equivFun_apply]

noncomputable def test (B : Basis I F K) (k : K) (side : Bool) :
    Vec (I × Bool) →ₗ[F] F :=
  ∑ i : I, B.repr k i • (LinearMap.proj (i,side) : Vec (I × Bool) →ₗ[F] F)

theorem test_apply (B : Basis I F K) (k : K) (side : Bool) (x : Vec (I × Bool)) :
    test B k side x = component side (tagChart B x k) := by
  classical
  cases side <;> simp [test,tagChart,Basis.constr_apply_fintype,component,target,
    LinearMap.sum_apply,LinearMap.smul_apply,Basis.equivFun_apply]

theorem rep_maps (s : Selection B priv tag) (height : Fin N → F × F)
    {x : Vec (I × Bool)} (ok : s.Eligible x) (i : I) :
    let e := s.rep i (target x i)
    priv e = B i ∧ tag e = tagChart B x (priv e) ∧ height e = lift s height x (priv e) := by
  obtain ⟨hk,ht⟩ := s.actual ok i
  exact ⟨hk,by simp [hk,tagChart,ht],by simp [hk,lift]⟩

#print axioms test_apply
#print axioms rep_maps
#print axioms Selection.actual
#print axioms code_read
end ExactPlaneRepresentativeLookup
