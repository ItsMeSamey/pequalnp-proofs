import ExactPlaneFeatureStream
namespace ExactPlaneFeatureStream
open ExactPlaneGaussianMaterialized Submodule
variable {P : Type*} {w : ℕ}

def prefixState (v : P→Vector F w) (xs : List P) : State w P := xs.foldl (step v) ([],[])

private theorem advance (v : P→Vector F w) (s : State w P) (x : P) :
    (step v s x).1=ExactPlaneGaussianMaterialized.insert s.1 (row v x) := by
  simp only [step,ExactPlaneGaussianMaterialized.insert]
  cases ExactPlaneGaussian.pivot (readRow (reduce s.1 (row v x))).1 <;> rfl

theorem prefix_spec (v : P→Vector F w) (xs : List P) :
    ExactPlaneGaussian.represented (readBank (prefixState v xs).1) =
      span F (features v '' sites xs) ∧
    ExactPlaneGaussian.Echelon (readBank (prefixState v xs).1) := by
  induction xs using List.reverseRecOn with
  | nil =>
    constructor
    · change (LinearMap.id : (Fin w→F) →ₗ[F] (Fin w→F)).ker=_
      simp [sites]
    · exact ExactPlaneGaussian.Echelon.nil
  | append_singleton xs x ih =>
    have eq : prefixState v (xs++[x])=step v (prefixState v xs) x := by simp [prefixState]
    have union : sites (xs++[x])=insert x (sites xs) := by ext p; simp [sites,or_comm]
    rw [eq,advance,read_insert]
    constructor
    · rw [ExactPlaneGaussian.insert_span,ih.1,union,Set.image_insert_eq,Submodule.span_insert,sup_comm]
      rfl
    · exact ExactPlaneGaussian.insert_echelon ih.2 _

theorem prefix_bank_bound (v : P→Vector F w) (xs : List P) :
    (prefixState v xs).1.length≤w := by
  simpa [readBank] using ExactPlaneGaussian.bank_length_le (prefix_spec v xs).2

private theorem zero_test (s : ExactPlaneGaussian.Bank w (Fin 0))
    (r : ExactPlaneGaussian.Row w (Fin 0)) :
    (ExactPlaneGaussian.reduce s r).1=0 ↔ r.1∈ExactPlaneGaussian.represented s := by
  induction s generalizing r with
  | nil => rfl
  | cons a s ih => exact ih (ExactPlaneGaussian.clear a.1 a.2 r)

theorem skip_dependent (v : P→Vector F w) (xs : List P) (x : P)
    (dep : features v x∈span F (features v '' sites xs)) :
    step v (prefixState v xs) x=prefixState v xs := by
  let st := prefixState v xs
  have mem : features v x∈ExactPlaneGaussian.represented (readBank st.1) :=
    (prefix_spec v xs).1.symm ▸ dep
  have zero : (readRow (reduce st.1 (row v x))).1=0 := by
    rw [read_reduce,zero_test]
    exact mem
  have none : ExactPlaneGaussian.pivot (readRow (reduce st.1 (row v x))).1=none := by
    rw [zero]; simp [ExactPlaneGaussian.pivot,List.find?_eq_none]
  change step v st x=st
  simp only [step,none]

theorem skip_equal (v : P→Vector F w) (xs : List P) (x earlier : P)
    (old : earlier∈xs) (equal : v x=v earlier) :
    step v (prefixState v xs) x=prefixState v xs := by
  apply skip_dependent
  apply Submodule.subset_span
  exact ⟨earlier,old,funext (fun j => congrArg (fun z : Vector F w => z[j]) equal.symm)⟩

#print axioms prefix_bank_bound
#print axioms skip_equal
end ExactPlaneFeatureStream
