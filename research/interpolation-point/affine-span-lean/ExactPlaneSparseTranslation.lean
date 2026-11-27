import ExactPlaneSectionCheckComplete
import Mathlib.Data.Finset.Fold
namespace ExactPlaneSparseTranslation
open ExactPlaneSparseANF ExactPlaneSparseValidation ExactPlaneAffineSpanHit
open ExactPlaneSectionCheckComplete ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial
open scoped BigOperators
variable {I : Type*} [DecidableEq I] [Fintype I]

noncomputable def read (s : Form I) (x : I→F) := eval (coeff s) (support x)
theorem read_plus (a b : Form I) (x : I→F) :
    read (plus a b) x=read a x+read b x := by simp only [read,eval,coeff_plus,Finset.sum_add_distrib]
theorem read_times (a b : Form I) (x : I→F) :
    read (times a b) x=read a x*read b x := by
  have eq := funext (coeff_times a b)
  simp only [read,eq,product_eval]
private theorem by_reads {a b : Form I} (h : ∀ x,read a x=read b x) : a=b :=
  ext_eval (fun A=>by simpa only [read,support_bits] using h (bits A))

private instance plusAssoc : Std.Associative (plus (I:=I)) :=
  ⟨fun _ _ _=>by apply by_reads; intro x; simp [read_plus,add_assoc]⟩
private instance plusComm : Std.Commutative (plus (I:=I)) :=
  ⟨fun _ _=>by apply by_reads; intro x; simp [read_plus,add_comm]⟩
private instance timesAssoc : Std.Associative (times (I:=I)) :=
  ⟨fun _ _ _=>by apply by_reads; intro x; simp [read_times,mul_assoc]⟩
private instance timesComm : Std.Commutative (times (I:=I)) :=
  ⟨fun _ _=>by apply by_reads; intro x; simp [read_times,mul_comm]⟩

private theorem singleton_read (U : Finset I) (x : I→F) :
    read {U} x = ∏ i∈U,x i := by
  by_cases all : U⊆support x
  · have on (i) (hi : i∈U) : x i=1 := (Finset.mem_filter.mp (all hi)).2
    simp [read,eval,coeff,all,Finset.prod_eq_one on]
  · obtain ⟨i,inside,off⟩ := Finset.not_subset.mp all
    have b : ∀ a:F,a=0 ∨ a=1 := by decide
    have z : x i=0 := (b _).resolve_right (fun e=>off (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩))
    simp [read,eval,coeff,all,Finset.prod_eq_zero inside z]

def shiftedMonomial (v : I→F) (U : Finset I) : Form I :=
  U.fold times {∅} (fun i=>plus {{i}} (constant (v i)))

private theorem monomial_read (v x : I→F) (U : Finset I) :
    read (shiftedMonomial v U) x=∏ i∈U,(x i+v i) := by
  induction U using Finset.induction_on with
  | empty => simp [shiftedMonomial,singleton_read]
  | @insert i s hi ih =>
    rw [shiftedMonomial,Finset.fold_insert hi,read_times,read_plus,singleton_read,Finset.prod_insert hi]
    change _ * read (shiftedMonomial v s) x=_
    rw [ih]
    simp [read,eval_constant]

def translate (v : I→F) (s : Form I) : Form I := s.fold plus ∅ (shiftedMonomial v)
theorem translate_read (v x : I→F) (s : Form I) :
    read (translate v s) x=read s (x+v) := by
  induction s using Finset.induction_on with
  | empty => simp [translate,read,eval_empty]
  | @insert U s hu ih =>
    have sp : insert U s=plus {U} s := by ext T; by_cases h:T=U <;> simp_all [plus]
    rw [translate,Finset.fold_insert hu,read_plus,monomial_read]
    change _ + read (translate v s) x=_
    rw [ih,sp,read_plus,singleton_read]
    rfl

theorem translate_eq_iff (v : I→F) (s : Form I) :
    translate v s=s ↔ ∀ x,read s (x+v)=read s x := by
  constructor
  · intro eq x; rw [←translate_read,eq]
  · intro h; apply by_reads; intro x; rw [translate_read,h]
#print axioms translate_eq_iff
end ExactPlaneSparseTranslation
