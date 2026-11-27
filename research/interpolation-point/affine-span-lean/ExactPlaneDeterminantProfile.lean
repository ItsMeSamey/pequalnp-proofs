import ExactPlaneAffineSubstitution
namespace ExactPlaneDeterminantProfile
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution
open scoped BigOperators
variable {J G : Type*} [Fintype J] [DecidableEq J] [Fintype G]
abbrev Pair (J : Type*) := Coeff J × Coeff J

noncomputable def detANF (f g : Pair J) : Coeff J :=
  fun U => product f.1 g.2 U + product g.1 f.2 U

theorem eval_det (f g : Pair J) (A : Finset J) : eval (detANF f g) A =
    eval f.1 A * eval g.2 A + eval g.1 A * eval f.2 A := by
  unfold eval detANF
  rw [Finset.sum_add_distrib]
  exact congrArg₂ (·+·) (product_eval _ _ _) (product_eval _ _ _)

def coordDegree (p : Coeff J) : ℕ :=
  Finset.univ.sup (fun U : Finset J => if p U=0 then 0 else U.card)

theorem coordDegree_le (p : Coeff J) (d : ℕ) :
    coordDegree p ≤ d ↔ degreeLE d p := by
  unfold coordDegree
  rw [Finset.sup_le_iff]
  constructor
  · intro low U high
    by_contra nz
    have bound := low U (Finset.mem_univ _)
    simpa [nz,high.not_ge] using bound
  · intro bound U _
    by_cases hi : d<U.card
    · simp [bound U hi]
    · split <;> omega

noncomputable def profile (f : G → Pair J) : ℕ :=
  Finset.univ.sup fun ij : G×G => coordDegree (detANF (f ij.1) (f ij.2))

theorem profile_le (f : G → Pair J) (d : ℕ) :
    profile f ≤ d ↔ ∀ i j, degreeLE d (detANF (f i) (f j)) := by
  unfold profile
  rw [Finset.sup_le_iff]
  constructor
  · intro h i j
    exact (coordDegree_le _ _).mp (h (i,j) (Finset.mem_univ _))
  · rintro h ⟨i,j⟩ _
    exact (coordDegree_le _ _).mpr (h i j)

theorem coordinates (f : G → Pair J) {j₁ j₂ : ℕ}
    (left : ∀ i, degreeLE j₁ (f i).1) (right : ∀ i, degreeLE j₂ (f i).2) :
    profile f ≤ j₁+j₂ := by
  apply (profile_le _ _).mpr
  intro i j U high
  simp only [detANF,product_degree _ _ (left i) (right j) U high,
    product_degree _ _ (left j) (right i) U high,add_zero]

def lc (a : G→F) (p : G→Coeff J) : Coeff J := fun U => ∑ i, a i*p i U

theorem eval_lc (a : G→F) (p : G→Coeff J) (A : Finset J) :
    eval (lc a p) A = ∑ i, a i * eval (p i) A := by
  unfold eval lc
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

noncomputable def expansion (f : G→Pair J) (a b : G→F) : Coeff J :=
  lc a fun i => lc b fun j => detANF (f i) (f j)

def combo (f : G→Pair J) (a : G→F) : Pair J :=
  (lc a fun i => (f i).1, lc a fun i => (f i).2)

private theorem lc_degree (a : G→F) (p : G→Coeff J) {d : ℕ}
    (h : ∀ i,degreeLE d (p i)) : degreeLE d (lc a p) := by
  intro U high
  simp [lc,fun i => h i U high]

theorem expansion_degree (f : G→Pair J) (a b : G→F) :
    degreeLE (profile f) (expansion f a b) := by
  have h := (profile_le f (profile f)).mp le_rfl
  exact lc_degree _ _ fun i => lc_degree _ _ (h i)

private theorem dist (a b X Y : G → F) :
    (∑ i, a i*X i)*(∑ j,b j*Y j) = ∑ i,a i*(∑ j,b j*(X i*Y j)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem expansion_eval (f : G→Pair J) (a b : G→F) (A : Finset J) :
    eval (expansion f a b) A = eval (detANF (combo f a) (combo f b)) A := by
  let X := fun i => eval (f i).1 A
  let Y := fun i => eval (f i).2 A
  simp only [expansion,eval_lc,eval_det,combo]
  change (∑ i,a i*(∑ j,b j*(X i*Y j+X j*Y i))) =
    (∑ i,a i*X i)*(∑ j,b j*Y j)+(∑ j,b j*X j)*(∑ i,a i*Y i)
  rw [mul_comm (∑ j,b j*X j) (∑ i,a i*Y i),dist,dist]
  simp only [mul_add,Finset.sum_add_distrib]
  simp only [mul_comm (X _) (Y _)]

private theorem eval_injective {p q : Coeff J} (h : ∀ A,eval p A=eval q A) : p=q := by
  funext U
  apply sub_eq_zero.mp
  apply (low_coeff_zero_iff_low_eval_zero (fun S => p S-q S) U.card).mpr _ U le_rfl
  intro A _
  change (∑ S ∈ A.powerset, (p S-q S))=0
  rw [Finset.sum_sub_distrib,sub_eq_zero]
  exact h A

theorem combination_degree (f : G→Pair J) (a b : G→F) :
    degreeLE (profile f) (detANF (combo f a) (combo f b)) := by
  rw [←eval_injective (expansion_eval f a b)]
  exact expansion_degree _ _ _

def constANF (c : F) : Coeff J := fun U => if U=∅ then c else 0

theorem eval_const (c : F) (A : Finset J) : eval (constANF c) A=c := by
  classical
  simp [eval,constANF]

def augmented (f : G→Pair J) : G ⊕ Bool → Pair J
  | .inl i => f i
  | .inr false => (constANF 1,constANF 0)
  | .inr true => (constANF 0,constANF 1)

theorem const_degree (c : F) (d : ℕ) : degreeLE d (constANF (J:=J) c) := by
  intro U high
  have ne : U≠∅ := by rintro rfl; simp at high
  simp [constANF,ne]

theorem augmented_coordinates (f : G → Pair J) {j₁ j₂ : ℕ}
    (left : ∀ i,degreeLE j₁ (f i).1) (right : ∀ i,degreeLE j₂ (f i).2) :
    profile (augmented f) ≤ j₁+j₂ := by
  apply coordinates
  · rintro (i|b)
    · exact left i
    · cases b <;> exact const_degree _ _
  · rintro (i|b)
    · exact right i
    · cases b <;> exact const_degree _ _

#print axioms combination_degree
#print axioms augmented_coordinates
end ExactPlaneDeterminantProfile
