import Research.DiagonalCompletion

namespace GuardRelease

open Matrix

abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- Inactive coordinates are fixed to zero. The active coordinates of the
supplied witness are one. -/
def chartValue {X I : Type*} {n : ℕ} (b : X → Bits n) (w : X)
    (S : Bits n ≃ₗ[ZMod 2] Bits n) (x : X) : Fin n ⊕ I → ZMod 2 :=
  Sum.elim (fun i => 1 + S (b x - b w) i) (fun _ => 0)

/-- The rows of A are the selected true guard alternatives after substituting
zero for all inactive pivots. A guard equation is required only when its
active pivot is one. The same diagonal choice and solver work for all x. -/
theorem cyclic_guard_chart {X I : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : X → Bits n) (w : X) (hw : A.mulVec (fun _ => 1) = b w) :
    ∃ (d : Bits n) (S : Bits n ≃ₗ[ZMod 2] Bits n),
      (∀ v, (A + diagonal d).mulVec (S v) = v) ∧
      chartValue (I := I) b w S w = Sum.elim (fun _ => 1) (fun _ => 0) ∧
      (∀ x (i : I), chartValue b w S x (.inr i) = 0) ∧
      ∀ x i, chartValue (I := I) b w S x (.inl i) = 1 →
        A.mulVec (fun j => chartValue (I := I) b w S x (.inl j)) i = b x i := by
  obtain ⟨d,S,hS⟩ := diagonal_linear_solver A
  refine ⟨d,S,hS,?_,fun _ _ => rfl,?_⟩
  · funext i
    cases i <;> simp [chartValue]
  · intro x i hi
    let v := S (b x - b w)
    have vi : v i = 0 := by
      change 1 + v i = 1 at hi
      simpa using hi
    have eqn := congrFun (hS (b x - b w)) i
    change (A + diagonal d).mulVec v i = (b x - b w) i at eqn
    rw [add_mulVec] at eqn
    have hdiag : (diagonal d).mulVec v i = d i * v i := by
      simp [mulVec, dotProduct, diagonal_apply]
    simp only [Pi.add_apply, Pi.sub_apply, hdiag, vi, mul_zero, add_zero] at eqn
    change A.mulVec ((fun _ => 1) + v) i = b x i
    rw [mulVec_add, hw, Pi.add_apply, eqn]
    abel

/-- Choose a guard separately in each active row from the alternatives that
hold at the witness. Each observed input uses the same selected alternatives. -/
theorem cyclic_disjunctive_guard_chart {X I : Type*} {n : ℕ} {G : Fin n → Type*}
    (a : (i : Fin n) → G i → Bits n) (b : (i : Fin n) → G i → X → ZMod 2)
    (w : X) (hw : ∀ i, ∃ j, dotProduct (a i j) (fun _ => 1) = b i j w) :
    ∃ (select : (i : Fin n) → G i) (S : Bits n ≃ₗ[ZMod 2] Bits n),
      let rhs := fun x i => b i (select i) x
      let value := chartValue (I := I) rhs w S
      value w = Sum.elim (fun _ => 1) (fun _ => 0) ∧
      (∀ x (i : I), value x (.inr i) = 0) ∧
      ∀ x i, value x (.inl i) = 1 →
        dotProduct (a i (select i)) (fun k => value x (.inl k)) = b i (select i) x := by
  classical
  let select := fun i => (hw i).choose
  let A : Matrix (Fin n) (Fin n) (ZMod 2) := fun i => a i (select i)
  let rhs := fun x i => b i (select i) x
  have hw' : A.mulVec (fun _ => 1) = rhs w := funext fun i => (hw i).choose_spec
  obtain ⟨_,S,_,pass,off,on⟩ := cyclic_guard_chart (I := I) A rhs w hw'
  exact ⟨select,S,pass,off,on⟩

end GuardRelease
