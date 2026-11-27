import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
namespace ExactPlaneWedgeProduct
abbrev F := ZMod 2
abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev V (n : ℕ) := Fin n → F
abbrev Alt (n : ℕ) := Pair n → F
abbrev Feature (n : ℕ) := F × V n × V n × Alt n
variable {n : ℕ}
def wedge (a b : V n) : Alt n := fun p =>
  a p.val.1 * b p.val.2 + a p.val.2 * b p.val.1
def actual (u v : V n) : Feature n := (1,u,v,wedge u v)
def multiply (a b : Feature n) : Feature n :=
  (a.1*b.1, b.1 • a.2.1 + a.1 • b.2.1,
   b.1 • a.2.2.1 + a.1 • b.2.2.1,
   b.1 • a.2.2.2 + a.1 • b.2.2.2 + wedge a.2.1 b.2.2.1 + wedge b.2.1 a.2.2.1)

local macro "feature_ext" : tactic =>
  `(tactic| (refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
            <;> first | funext i | skip))

def bilinear (n : ℕ) : Feature n →ₗ[F] Feature n →ₗ[F] Feature n :=
  LinearMap.mk₂ F multiply
    (by intro a b c; feature_ext <;> simp [multiply,wedge,smul_eq_mul] <;> ring)
    (by intro z a b; feature_ext <;> simp [multiply,wedge,smul_eq_mul] <;> ring)
    (by intro a b c; feature_ext <;> simp [multiply,wedge,smul_eq_mul] <;> ring)
    (by intro z a b; feature_ext <;> simp [multiply,wedge,smul_eq_mul] <;> ring)

theorem actual_join (u v x y : V n) :
    bilinear n (actual u v) (actual x y) = actual (u+x) (v+y) := by
  change multiply _ _ = _
  feature_ext <;> simp [multiply,actual,wedge,smul_eq_mul] <;> ring

theorem retained_span (L R L' R' : Set (Feature n))
    (left : Submodule.span F L'=Submodule.span F L)
    (right : Submodule.span F R'=Submodule.span F R) :
    Submodule.span F (Set.image2 (fun x y=>bilinear n x y) L' R') =
    Submodule.span F (Set.image2 (fun x y=>bilinear n x y) L R) := by
  rw [←Submodule.map₂_span_span,←Submodule.map₂_span_span,left,right]

theorem witnesses {P Q : Type*} (f : P→Feature n) (g : Q→Feature n)
    (L L' : Set P) (R R' : Set Q)
    (lsub : L'⊆L) (rsub : R'⊆R)
    (ls : Submodule.span F (f '' L')=Submodule.span F (f '' L))
    (rs : Submodule.span F (g '' R')=Submodule.span F (g '' R))
    (test : Feature n→ₗ[F] F) (x : P) (hx : x∈L) (y : Q) (hy : y∈R)
    (hit : test (bilinear n (f x) (g y)) ≠ 0) :
    ∃ i∈L', ∃ j∈R', i∈L ∧ j∈R ∧ test (bilinear n (f i) (g j)) ≠ 0 := by
  classical
  by_contra! fail
  have small : Submodule.span F (Set.image2 (fun a b=>bilinear n a b) (f '' L') (g '' R')) ≤ LinearMap.ker test := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨i,hi,rfl⟩,_,⟨j,hj,rfl⟩,rfl⟩
    exact fail i hi j hj (lsub hi) (rsub hj)
  rw [retained_span _ _ _ _ ls rs] at small
  exact hit (small (Submodule.subset_span ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩))

/-- Choose independent original payloads even when several have equal features. -/
theorem retain {P : Type*} (f : P→Feature n) (S : Finset P) :
    ∃ T : Finset P, T⊆S ∧ LinearIndepOn F f (T : Set P) ∧
      Submodule.span F (f '' (T : Set P)) = Submodule.span F (f '' (S : Set P)) := by
  classical
  let empty := linearIndepOn_empty F f
  let inc := Set.empty_subset (S : Set P)
  let T := empty.extend inc
  have sub : T ⊆ (S : Set P) := empty.extend_subset inc
  have finite : T.Finite := S.finite_toSet.subset sub
  refine ⟨finite.toFinset,?_,?_,?_⟩
  · intro x hx; exact sub (finite.mem_toFinset.mp hx)
  · simpa only [Set.Finite.coe_toFinset] using empty.linearIndepOn_extend inc
  · simpa only [Set.Finite.coe_toFinset] using empty.span_image_extend_eq_span_image inc

#print axioms actual_join
#print axioms retained_span
#print axioms witnesses
end ExactPlaneWedgeProduct
