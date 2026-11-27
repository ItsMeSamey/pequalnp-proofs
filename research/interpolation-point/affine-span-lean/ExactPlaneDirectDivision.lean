import ExactPlaneIrreducibleSearch
import ExactPlaneBinaryArithmetic
namespace ExactPlaneDirectDivision
open ExactPlaneIrreducibleSearch
open scoped BigOperators

def materialize {a : ℕ} (u : Word a) : Word a :=
  let data := List.ofFn u
  fun i => data[i.val]?.getD 0

@[simp] theorem materialize_eq {a : ℕ} (u : Word a) : materialize u = u := by
  funext i
  simp [materialize,i.isLt]

/-- Horner division with an a-bit remainder, realized before the next shift. -/
def remWord {a : ℕ} (c : Word a) : (n : ℕ) → Word n → Word a
  | 0, _ => 0
  | n+1, f => materialize
      (f 0 • ExactPlaneBinaryArithmetic.unit 0 +
        ExactPlaneBinaryArithmetic.step c (remWord c n (fun i => f i.succ)))

theorem encode_rem {P : Polynomial F} (hm : P.Monic) (hp : 0<P.natDegree)
    (n : ℕ) (f : Word n) :
    ExactPlaneBinaryArithmetic.encode hm (remWord (fun i : Fin P.natDegree => -P.coeff i.val) n f) =
    ∑ i : Fin n, f i • (AdjoinRoot.root P)^i.val := by
  induction n with
  | zero => simp [remWord]
  | succ n ih =>
    rw [remWord,materialize_eq,map_add,map_smul,ExactPlaneBinaryArithmetic.encode_unit hm 0 hp,
      ExactPlaneBinaryArithmetic.encode_step,ih,Fin.sum_univ_succ,Finset.sum_mul]
    simp only [Fin.val_zero,Fin.val_succ,pow_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc,pow_succ]

def divides {a n : ℕ} (u : Word a) (w : Word n) : Bool :=
  decide (remWord (-u) (n+1) (fun i => coeff w i.val) = 0)

private theorem test {P : Polynomial F} (hm : P.Monic) (hp : 0<P.natDegree)
    {n : ℕ} (w : Word n) :
    remWord (fun i : Fin P.natDegree => -P.coeff i.val) (n+1) (fun i => coeff w i.val) = 0 ↔ P ∣ poly w := by
  have eval : ExactPlaneBinaryArithmetic.encode hm
      (remWord (fun i : Fin P.natDegree => -P.coeff i.val) (n+1) (fun i => coeff w i.val)) =
      AdjoinRoot.mk P (poly w) := by
    rw [encode_rem hm hp]
    unfold poly
    rw [Polynomial.ofFn_eq_sum_monomial,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp [Algebra.smul_def,AdjoinRoot.algebraMap_eq]
  rw [←AdjoinRoot.mk_eq_zero,←eval]
  exact (ExactPlaneBinaryArithmetic.encode hm).map_eq_zero_iff.symm

private theorem test_at {P : Polynomial F} (hm : P.Monic) {a n : ℕ}
    (hd : P.natDegree=a) (hp : 0<a) (u : Word a) (w : Word n)
    (low : ∀ i : Fin a, P.coeff i.val = u i) :
    divides u w=true ↔ P ∣ poly w := by
  subst a
  have co : (fun i : Fin P.natDegree => -P.coeff i.val) = -u :=
    funext fun i => congrArg Neg.neg (low i)
  simpa only [divides,decide_eq_true_eq,co] using test hm hp w

theorem divides_iff {a n : ℕ} (u : Word a) (w : Word n) (apos : 0<a) :
    divides u w=true ↔ poly u ∣ poly w := by
  apply test_at (monic u) (degree u) apos
  intro i
  simp [poly_coeff,coeff,i.isLt]

def good {n : ℕ} (w : Word n) : Bool :=
  (List.range (n/2)).all fun j => (words (j+1)).all fun u => !(divides u w)

def fastFind (n : ℕ) : Option (Word n) := (words n).find? good

theorem good_iff {n : ℕ} (hn : 0<n) (w : Word n) :
    good w=true ↔ Irreducible (poly w) := by
  simp only [good,List.all_eq_true,List.mem_range,Bool.not_eq_true',mem_words,true_implies]
  rw [(monic w).irreducible_iff_natDegree']
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro eq
      have hd := congrArg Polynomial.natDegree eq
      simp [degree] at hd
      omega
    · intro f g hf hg eq small
      obtain ⟨pos,small⟩ := Finset.mem_Ioc.mp small
      rw [degree] at small
      obtain ⟨u,hu⟩ := covers (n:=g.natDegree-1+1) g hg (by omega)
      have yes := (divides_iff u w (by omega)).2 (by rw [hu]; exact ⟨f,by rw [mul_comm,eq]⟩)
      have no := h (g.natDegree-1) (by omega) u
      simp_all
  · rintro ⟨_,no⟩ t ht u
    cases eq : divides u w with
    | false => rfl
    | true =>
      obtain ⟨v,hv⟩ := (divides_iff u w (by omega)).1 eq
      have hm : v.Monic := (monic u).of_mul_monic_left (hv ▸ monic w)
      have bad := no v (poly u) hm (monic u) (by rw [mul_comm]; exact hv.symm)
      exfalso
      apply bad
      rw [Finset.mem_Ioc,degree,degree]
      omega

theorem fastFind_eq (n : ℕ) (hn : 0<n) : fastFind n=ExactPlaneIrreducibleSearch.find n := by
  have same : @good n = @ExactPlaneIrreducibleSearch.good n := by
    funext w
    have eq := (good_iff hn w).trans (ExactPlaneIrreducibleSearch.good_iff hn w).symm
    cases h : good w <;> cases j : ExactPlaneIrreducibleSearch.good w <;> simp_all
  simp [fastFind,ExactPlaneIrreducibleSearch.find,same]

#print axioms fastFind_eq
end ExactPlaneDirectDivision
