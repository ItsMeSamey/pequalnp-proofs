import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod

namespace ExactPlanePhysicalResidual
open scoped BigOperators
abbrev F := ZMod 2
variable {I J K B H : Type*} [AddCommGroup K] [Module F K]
  [AddCommGroup B] [Module F B] [AddCommGroup H] [Module F H]

def col (k : I → K) (b : I → B) (h : I → H) (i : I) : K × B × H := (k i,b i,h i)

def indexedSpan {V : Type*} [AddCommGroup V] [Module F V]
    (A : Finset I) (v : I → V) : Submodule F V := Submodule.span F (v '' (A : Set I))

def residual (k : I → K) (h : I → H) (L : K →ₗ[F] H) (i : I) :=
  h i + L (k i)

noncomputable def basisLift (e : Module.Basis J F K) (a : J → I) (h : I → H) : K →ₗ[F] H :=
  e.constr F (fun j => h (a j))

theorem basisLift_spec (e : Module.Basis J F K) (a : J → I) (h : I → H) (j : J) :
    basisLift e a h (e j) = h (a j) := e.constr_basis F _ _

private theorem self_add {V : Type*} [AddCommGroup V] [Module F V] (v : V) : v+v=0 := by
  have z : (1:F)+1=0 := by decide
  calc
    v+v = ((1:F)+1) • v := by simp [add_smul]
    _ = 0 := by rw [z,zero_smul]

private def graphMap (g : K →ₗ[F] B) (L : K →ₗ[F] H) : K →ₗ[F] K × B × H :=
  LinearMap.id.prod (g.prod L)

private def vertical : H →ₗ[F] K × B × H :=
  (0 : H →ₗ[F] K).prod ((0 : H →ₗ[F] B).prod LinearMap.id)

private def strip (L : K →ₗ[F] H) : (K × B × H) →ₗ[F] H :=
  (LinearMap.snd F B H).comp (LinearMap.snd F K (B × H)) + L.comp (LinearMap.fst F K (B × H))

private def mismatch (g : K →ₗ[F] B) : (K × B × H) →ₗ[F] B :=
  (LinearMap.fst F B H).comp (LinearMap.snd F K (B × H)) - g.comp (LinearMap.fst F K (B × H))

theorem span_iff [Fintype J] (A : Finset I) (k : I → K) (b : I → B) (h : I → H)
    (g : K →ₗ[F] B) (L : K →ₗ[F] H)
    (matched : ∀ i∈A, b i=g (k i))
    (e : Module.Basis J F K) (a : J → I) (inside : ∀ j, a j∈A)
    (ka : ∀ j, k (a j)=e j) (ha : ∀ j, h (a j)=L (e j))
    (x : K) (y : B) (z : H) :
    (x,y,z) ∈ indexedSpan A (col k b h) ↔
      y=g x ∧ z + L x ∈ indexedSpan A (residual k h L) := by
  classical
  let S := indexedSpan A (col k b h)
  let T := indexedSpan A (residual k h L)
  have phys (i : I) (hi : i∈A) : col k b h i ∈ S :=
    Submodule.subset_span ⟨i,hi,rfl⟩
  have graph (u : K) : graphMap g L u ∈ S := by
    rw [← e.sum_repr u]
    rw [map_sum]
    apply S.sum_mem
    intro j _
    rw [map_smul]
    apply S.smul_mem
    have id : graphMap g L (e j)=col k b h (a j) := by
      change (e j,g (e j),L (e j))=(k (a j),b (a j),h (a j))
      rw [matched _ (inside j),ka,ha]
    rw [id]
    exact phys _ (inside j)
  have liftT : T ≤ S.comap (vertical (K:=K) (B:=B)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change (0,0,residual k h L i) ∈ S
    have add := S.add_mem (phys i hi) (graph (k i))
    change (k i+k i,b i+g (k i),h i+L (k i)) ∈ S at add
    simpa [residual,matched i hi,self_add] using add
  constructor
  · intro hx
    have keep : S ≤ T.comap (strip L) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,hi,rfl⟩
      exact Submodule.subset_span ⟨i,hi,rfl⟩
    have agree : S ≤ LinearMap.ker (mismatch g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,hi,rfl⟩
      change b i - g (k i)=0
      exact sub_eq_zero.mpr (matched i hi)
    exact ⟨sub_eq_zero.mp (show y - g x=0 from agree hx),keep hx⟩
  · rintro ⟨rfl, hz⟩
    have add := S.add_mem (graph x) (liftT hz)
    change (x+0,g x+0,L x+(z+L x)) ∈ S at add
    have reduce : L x+(z+L x)=z := calc
      _ = z+(L x+L x) := by ac_rfl
      _ = z := by rw [self_add,add_zero]
    simpa only [add_zero,reduce] using add

theorem physical_support {V : Type*} [AddCommGroup V] [Module F V] (A : Finset I)
    (v : I → V) (z : V) :
    z ∈ indexedSpan A v ↔ ∃ U : Finset I, U ⊆ A ∧ ∑ i ∈ U, v i = z := by
  classical
  constructor
  · intro hz
    obtain ⟨c,hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R:=F)).mp hz
    refine ⟨A.filter (fun i => c i=1),Finset.filter_subset _ _,?_⟩
    rw [Finset.sum_filter,← hc]
    apply Finset.sum_congr rfl
    intro i _
    have bit : ∀ t : F, t=0 ∨ t=1 := by decide
    rcases bit (c i) with hi|hi <;> simp [hi]
  · rintro ⟨U,sub,rfl⟩
    exact (indexedSpan A v).sum_mem fun i hi => Submodule.subset_span ⟨i,sub hi,rfl⟩

theorem neutral_support [Fintype J] (A : Finset I) (k : I → K) (b : I → B) (h : I → H)
    (g : K →ₗ[F] B) (L : K →ₗ[F] H) (matched : ∀ i∈A, b i=g (k i))
    (e : Module.Basis J F K) (a : J → I) (inside : ∀ j, a j∈A)
    (ka : ∀ j, k (a j)=e j) (ha : ∀ j, h (a j)=L (e j)) (r : H) :
    r ∈ indexedSpan A (residual k h L) ↔
      ∃ U : Finset I, U ⊆ A ∧ ∑ i ∈ U, col k b h i = (0,0,r) := by
  rw [← physical_support]
  simpa using (span_iff A k b h g L matched e a inside ka ha 0 0 r).symm

theorem independent_supports [Fintype J] (A : Finset I) (k : I → K) (b : I → B)
    (h : I → H) (g : K →ₗ[F] B) (L : K →ₗ[F] H) (matched : ∀ i∈A, b i=g (k i))
    (e : Module.Basis J F K) (a : J → I) (inside : ∀ j, a j∈A)
    (ka : ∀ j, k (a j)=e j) (ha : ∀ j, h (a j)=L (e j))
    (r : Fin 2 → H) (indep : LinearIndependent F r)
    (hit : ∀ j, r j ∈ indexedSpan A (residual k h L)) :
    ∃ U : Fin 2 → Finset I, (∀ j, U j ⊆ A) ∧
      (∀ j, ∑ i ∈ U j, col k b h i = (0,0,r j)) ∧ U 0 ≠ U 1 := by
  classical
  choose U sub realizes using fun j =>
    (neutral_support A k b h g L matched e a inside ka ha (r j)).mp (hit j)
  refine ⟨U,sub,realizes,?_⟩
  intro same
  have eq := (realizes 0).symm.trans ((congrArg (fun S : Finset I =>
    ∑ i ∈ S, col k b h i) same).trans (realizes 1))
  have hr : r 0=r 1 := congrArg (fun p : K × B × H => p.2.2) eq
  exact (by decide : (0:Fin 2)≠1) (indep.injective hr)

#print axioms span_iff
#print axioms physical_support
#print axioms neutral_support
#print axioms independent_supports
end ExactPlanePhysicalResidual
