import ExactPlaneEagerCounts
namespace ExactPlaneClearWork
open ExactPlanePhysicalConverse ExactPlaneGaussianMaterialized ExactPlaneEagerCounts

/-- Count coordinate additions in the two eager vectors only when the pivot bit is nonzero. -/
def reduceWork {w n : ℕ} : Bank w n → Row w n → Row w n × ℕ
  | [],r => (r,0)
  | (i,p)::s,r =>
    if r.1[i]=0 then reduceWork s r
    else
      let next : Row w n := (Vector.ofFn (fun j : Fin w => r.1[j]+p.1[j]),
        Vector.ofFn (fun j : Fin n => r.2[j]+p.2[j]))
      let z := reduceWork s next
      (z.1,z.2+(w+n))

theorem reduceWork_spec {w n : ℕ} (s : Bank w n) (r : Row w n) :
    (reduceWork s r).1=reduce s r ∧ (reduceWork s r).2≤(reduceC s r).2*(w+n) := by
  rw [reduceC_eq]
  induction s generalizing r with
  | nil => simp [reduceWork,reduce]
  | cons a s ih =>
    rcases a with ⟨i,p⟩
    by_cases hz : r.1[i]=0
    · simp only [reduceWork,hz,ite_true,reduce,clear,List.length_cons]
      exact ⟨(ih r).1,(ih r).2.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩
    · let next : Row w n := (Vector.ofFn (fun j : Fin w => r.1[j]+p.1[j]),
          Vector.ofFn (fun j : Fin n => r.2[j]+p.2[j]))
      simp only [reduceWork,hz,ite_false,reduce,clear,List.length_cons,Nat.add_mul,one_mul]
      exact ⟨(ih next).1,Nat.add_le_add_right (ih next).2 _⟩

#print axioms reduceWork_spec
end ExactPlaneClearWork
