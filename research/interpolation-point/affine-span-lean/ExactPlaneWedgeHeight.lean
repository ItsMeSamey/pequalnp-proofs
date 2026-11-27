import ExactPlaneWedgeProduct
import ExactPlaneRelationPair
namespace ExactPlaneWedgeHeight
open ExactPlaneWedgeProduct ExactPlaneResidualPivots ExactPlaneFirstRelation
open scoped BigOperators
variable {n : Nat}

def cross (i j : Fin n) (x : Feature n) : F :=
  if a : i < j then x.2.2.2 ⟨(i,j),a⟩ else if b : j < i then x.2.2.2 ⟨(j,i),b⟩ else 0

def score (h : Fin n → Plane) (x : Feature n) : F :=
  ∑ i, ∑ j, (h i).1 * (h j).2 * cross i j x

def linear (h : Fin n → Plane) : Feature n →ₗ[F] F where
  toFun := score h
  map_add' x y := by
    unfold score
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases a : i < j <;> by_cases b : j < i <;> simp [cross,a,b,mul_add]
  map_smul' c x := by
    change score h (c • x) = c * score h x
    unfold score
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases a : i < j <;> by_cases b : j < i <;> simp [cross,a,b,smul_eq_mul] <;> ring

theorem cross_actual (i j : Fin n) (u v : V n) :
    cross i j (actual u v) = u i*v j + v i*u j := by
  rcases lt_trichotomy i j with a|eq|b
  · simp [cross,a,actual,wedge,mul_comm]
  · subst j
    have cancel : ∀ z : F,z+z=0 := by decide
    simp [cross,mul_comm,cancel]
  · simp [cross,not_lt_of_gt b,b,actual,wedge,mul_comm,add_comm]

private theorem ag (h : Fin n→Plane) (u : V n) :
    aggregate h u=(∑ i,u i*(h i).1, ∑ i,u i*(h i).2) := by
  unfold aggregate
  rw [LinearMap.sum_apply]
  apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum,smul_eq_mul]

theorem score_actual (h : Fin n→Plane) (u v : V n) :
    score h (actual u v) = det (aggregate h u) (aggregate h v) := by
  unfold score
  rw [Finset.sum_comm]
  simp only [cross_actual,ag,det,Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
#print axioms score_actual
end ExactPlaneWedgeHeight
