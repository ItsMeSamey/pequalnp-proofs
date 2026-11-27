import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Domain

namespace ExactPlaneIrreducibleSearch
open scoped BigOperators
abbrev F := ZMod 2
abbrev Word (n : ℕ) := Fin n → F

def coeff {n : ℕ} (w : Word n) (i : ℕ) : F :=
  if h : i<n then w ⟨i,h⟩ else if i=n then 1 else 0

def words : (n : ℕ) → List (Word n)
  | 0 => [Fin.elim0]
  | n+1 => (words n).flatMap (fun w => [Fin.cons 0 w,Fin.cons 1 w])

theorem mem_words {n : ℕ} (w : Word n) : w∈words n := by
  induction n with
  | zero =>
    have eq : w=Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [words,eq]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨fun i => w i.succ,ih _,?_⟩
    have bit : ∀ b : F,b=0 ∨ b=1 := by decide
    have eq : Fin.cons (w 0) (fun i => w i.succ)=w := funext (Fin.cases rfl (fun _ => rfl))
    rcases bit (w 0) with he|he <;> rw [he] at eq <;> simp [eq]

theorem words_length (n : ℕ) : (words n).length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have double (l : List (Word n)) : (l.flatMap (fun w : Word n => [(Fin.cons 0 w : Word (n+1)),Fin.cons 1 w])).length =
        l.length*2 := by
      induction l with
      | nil => rfl
      | cons a l h => simp [h,Nat.add_mul,Nat.add_comm] <;> omega
    rw [words,double,ih,pow_succ]

noncomputable def poly {n : ℕ} (w : Word n) : Polynomial F :=
  Polynomial.ofFn (n+1) (fun i => coeff w i.val)

theorem poly_coeff {n : ℕ} (w : Word n) (j : ℕ) : (poly w).coeff j=coeff w j := by
  by_cases h : j<n+1
  · exact Polynomial.ofFn_coeff_eq_val_of_lt _ h
  · rw [poly,Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt h)]
    simp [coeff,show ¬j<n by omega,show j≠n by omega]

private theorem degree_le {n : ℕ} (w : Word n) : (poly w).natDegree ≤ n := by
  have h := Polynomial.ofFn_natDegree_lt (R:=F) (n:=n+1) (by omega)
    (fun i : Fin (n+1) => coeff w i.val)
  change (poly w).natDegree < n+1 at h
  omega

theorem degree {n : ℕ} (w : Word n) : (poly w).natDegree=n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (degree_le w)
  simp [poly_coeff,coeff]

theorem monic {n : ℕ} (w : Word n) : (poly w).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n (degree_le w)
  simp [poly_coeff,coeff]

theorem covers {n : ℕ} (p : Polynomial F) (hp : p.Monic) (hn : p.natDegree=n) :
    ∃ w : Word n, poly w=p := by
  refine ⟨fun i => p.coeff i.val,?_⟩
  ext j
  rw [poly_coeff]
  by_cases lt : j<n
  · simp [coeff,lt]
  · by_cases eq : j=n
    · subst j
      simpa [coeff,← hn] using hp.coeff_natDegree.symm
    · have high : p.natDegree < j := by omega
      simp [coeff,lt,eq,Polynomial.coeff_eq_zero_of_natDegree_lt high]

def conv {a b : ℕ} (u : Word a) (v : Word b) (i : ℕ) : F :=
  ∑ ij ∈ Finset.antidiagonal i,coeff u ij.1 * coeff v ij.2

def productMatch {n a b : ℕ} (w : Word n) (u : Word a) (v : Word b) : Bool :=
  decide (∀ i : Fin (n+1), conv u v i.val=coeff w i.val)

theorem productMatch_iff {n a b : ℕ} (w : Word n) (u : Word a) (v : Word b) (sizes : a+b=n) :
    productMatch w u v=true ↔ poly u * poly v=poly w := by
  have mulCoeff (j : ℕ) : (poly u * poly v).coeff j=conv u v j := by
    simp [Polynomial.coeff_mul,conv,poly_coeff]
  have degreeProd : (poly u * poly v).natDegree=n := by
    rw [Polynomial.natDegree_mul (monic u).ne_zero (monic v).ne_zero,degree,degree,sizes]
  simp only [productMatch,decide_eq_true_eq]
  constructor
  · intro h
    ext j
    by_cases small : j<n+1
    · rw [mulCoeff,poly_coeff]
      exact h ⟨j,small⟩
    · have hj : n<j := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (degreeProd.trans_lt hj),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((degree w).trans_lt hj)]
  · intro eq i
    simpa only [mulCoeff,poly_coeff] using congrArg (fun p : Polynomial F => p.coeff i.val) eq

def good {n : ℕ} (w : Word n) : Bool :=
  (List.range (n/2)).all fun t =>
    (words (t+1)).all fun u =>
      (words (n-(t+1))).all fun v => !(productMatch w u v)

def find (n : ℕ) : Option (Word n) := (words n).find? good

private theorem good_spec {n : ℕ} (w : Word n) :
    good w=true ↔ ∀ t<n/2, ∀ u : Word (t+1), ∀ v : Word (n-(t+1)),
      productMatch w u v≠true := by
  simp [good,List.all_eq_true,mem_words]

theorem good_iff {n : ℕ} (hn : 0<n) (w : Word n) :
    good w=true ↔ Irreducible (poly w) := by
  rw [good_spec,(monic w).irreducible_iff_natDegree']
  constructor
  · intro test
    constructor
    · intro eq
      have h := congrArg Polynomial.natDegree eq
      simp [degree] at h
      omega
    · intro f g hf hg eq small
      obtain ⟨pos,small⟩ := Finset.mem_Ioc.mp small
      rw [degree] at small
      have sum : f.natDegree + g.natDegree=n := by
        rw [←Polynomial.natDegree_mul hf.ne_zero hg.ne_zero,eq,degree]
      let t := g.natDegree-1
      have dt : t+1=g.natDegree := by dsimp [t]; omega
      have ht : t<n/2 := by omega
      obtain ⟨u,hu⟩ := covers g hg dt.symm
      obtain ⟨v,hv⟩ := covers (n:=n-(t+1)) f hf (by omega)
      apply test t ht u v
      apply (productMatch_iff _ _ _ (by omega)).mpr
      rw [hu,hv,mul_comm,eq]
  · rintro ⟨_,no⟩ t ht u v eq
    have factor := (productMatch_iff w u v (by omega)).mp eq
    have bad := no (poly v) (poly u) (monic v) (monic u) (by rw [mul_comm]; exact factor)
    apply bad
    rw [Finset.mem_Ioc,degree,degree]
    omega

theorem find_sound {n : ℕ} (hn : 0<n) {w : Word n} (found : find n=some w) :
    (poly w).Monic ∧ (poly w).natDegree=n ∧ Irreducible (poly w) := by
  exact ⟨monic w,degree w,(good_iff hn w).mp (List.find?_some (p:=good) found)⟩

theorem find_complete_of_exists {n : ℕ} (hn : 0<n)
    (exists_poly : ∃p : Polynomial F,p.Monic ∧ p.natDegree=n ∧ Irreducible p) :
    ∃ w,find n=some w := by
  obtain ⟨p,mon,deg,irr⟩ := exists_poly
  obtain ⟨u,hu⟩ := covers p mon deg
  have pass := (good_iff hn u).mpr (hu ▸ irr)
  cases h : find n with
  | some w => exact ⟨w,rfl⟩
  | none =>
    unfold find at h
    have fail := List.find?_eq_none.mp h u (mem_words u)
    simp [pass] at fail

#print axioms good_iff
#print axioms find_sound
end ExactPlaneIrreducibleSearch
