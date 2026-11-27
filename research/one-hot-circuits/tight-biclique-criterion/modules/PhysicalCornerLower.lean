import FormulaCorner

namespace OnePerShore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def pairFlags (i j k : ℕ) : Bool := decide (k=i) || decide (k=j)

private theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = pairFlags u.val (n+v.val) i := by
  by_cases hn : i<n
  · have ne : i ≠ n+v.val := by omega
    have fin : (⟨i,hn⟩ : Fin n) = u ↔ i=u.val := Fin.ext_iff
    simp [pairFlags,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,hn,ne,fin]
  · have ne : i ≠ u.val := by omega
    by_cases hm : i-n<m
    · have fin : (⟨i-n,hm⟩ : Fin m) = v ↔ i=n+v.val := by
        rw [Fin.ext_iff]; change i-n=v.val ↔ _; omega
      simp [pairFlags, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        Nat.le_of_not_gt hn, ne, hm, fin]
    · have ne' : i ≠ n+v.val := by omega
      simp [pairFlags, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        Nat.le_of_not_gt hn, ne, hm, ne']

private theorem Formula.eval_mono (t : Formula) (x y : ℕ → Bool)
    (h : ∀ i, x i = true → y i = true) : t.eval x = true → t.eval y = true := by
  induction t with
  | atom i => exact h i
  | node op l r hl hr =>
    cases op <;> simp only [Formula.eval,Bool.false_eq_true,ite_false,ite_true,
      Bool.and_eq_true,Bool.or_eq_true] <;> tauto

/-- A missing corner on nonuniversal vertices raises the physical gate
floor by one. The missing corner itself witnesses two nonuniversal flags. -/
theorem physical_corner_lower {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (u w : Fin n) (v z : Fin m)
    (uv : A u v = true) (uz : A u z = true) (wv : A w v = true) (wz : A w z = false)
    (u_nonuniv : ∃ j, A u j = false) (v_nonuniv : ∃ i, A i v = false)
    (bound : RepSizeAtMost A s) : charged A ≤ s := by
  by_contra h
  obtain ⟨C,legal,size,rep⟩ := bound
  obtain ⟨t,nd,_,sem⟩ := formula_of_tight_circuit legal rep (by omega) (by omega)
  have trep (i : Fin n) (j : Fin m) : t.eval (pairFlags i.val (n+j.val)) = A i j := by
    have he := sem (oneEach i j) (by simp [oneEach])
    simpa only [oneEach_getD, rep i j] using he
  have row (i : Fin n) (j : Fin m) (zero : A i j = false) :
      t.eval (fun k => decide (k=i.val)) = false := by
    cases he : t.eval (fun k => decide (k=i.val)) with
    | false => rfl
    | true =>
      have z := t.eval_mono _ (pairFlags i.val (n+j.val)) (fun k hk => by simp [pairFlags,hk]) he
      simp [trep i j,zero] at z
  have col (i : Fin n) (j : Fin m) (zero : A i j = false) :
      t.eval (fun k => decide (k=n+j.val)) = false := by
    cases he : t.eval (fun k => decide (k=n+j.val)) with
    | false => rfl
    | true =>
      have z := t.eval_mono _ (pairFlags i.val (n+j.val)) (fun k hk => by simp [pairFlags,hk]) he
      simp [trep i j,zero] at z
  obtain ⟨j,hj⟩ := u_nonuniv
  obtain ⟨i,hi⟩ := v_nonuniv
  apply t.no_corner nd u.val w.val (n+v.val) (n+z.val)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (row u j hj)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (row w z wz)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (col i v hi)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (col w z wz)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep u v).trans uv)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep u z).trans uz)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep w v).trans wv)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep w z).trans wz)

end OnePerShore
