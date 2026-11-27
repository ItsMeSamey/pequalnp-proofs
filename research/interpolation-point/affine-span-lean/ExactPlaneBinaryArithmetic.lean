import ExactPlaneFieldSampler
import Mathlib.RingTheory.AdjoinRoot
namespace ExactPlaneBinaryArithmetic
open Polynomial Module
open scoped BigOperators
abbrev F := ZMod 2
abbrev Word (r : ℕ) := Fin r → F

def unit {r : ℕ} (j : ℕ) : Word r := fun i => if i.val=j then 1 else 0

def step {r : ℕ} (c x : Word r) : Word r :=
  ∑ i : Fin r,x i • (if i.val+1 < r then unit (i.val+1) else c)

def shifts {r : ℕ} (c x : Word r) : ℕ → Word r
  | 0 => x
  | n+1 => step c (shifts c x n)

def mul {r : ℕ} (c x y : Word r) : Word r :=
  ∑ i : Fin r,x i • shifts c y i.val

def power {r : ℕ} (c x : Word r) : ℕ → Word r
  | 0 => unit 0
  | n+1 => mul c (power c x n) x

variable {P : Polynomial F}
noncomputable def encode (hm : P.Monic) : Word P.natDegree ≃ₗ[F] AdjoinRoot P :=
  (AdjoinRoot.powerBasisAux' hm).equivFun.symm

theorem encode_sum (hm : P.Monic) (x : Word P.natDegree) :
    encode hm x = ∑ i : Fin P.natDegree,x i • AdjoinRoot.root P ^ i.val := by
  unfold encode
  rw [Basis.equivFun_symm_apply]
  have hb (i : Fin P.natDegree) : AdjoinRoot.powerBasisAux' hm i = AdjoinRoot.root P ^ i.val :=
    (AdjoinRoot.powerBasis' hm).basis_eq_pow i
  simp only [hb]

theorem encode_unit (hm : P.Monic) (j : ℕ) (hj : j < P.natDegree) :
    encode hm (unit j) = AdjoinRoot.root P ^ j := by
  rw [encode_sum,Finset.sum_eq_single (⟨j,hj⟩ : Fin P.natDegree)]
  · simp [unit]
  · intro i _ ne
    have hn : i.val ≠ j := fun h => ne (Fin.ext h)
    simp [unit,hn]
  · simp

theorem encode_modulus (hm : P.Monic) :
    encode hm (fun i => -P.coeff i.val) = AdjoinRoot.root P ^ P.natDegree := by
  have eq := congrArg (aeval (AdjoinRoot.root P)) P.as_sum_range_C_mul_X_pow
  rw [Finset.sum_range_succ] at eq
  simp only [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self,map_add,map_sum,map_mul,map_pow,
    AdjoinRoot.mk_C,AdjoinRoot.mk_X,coeff_natDegree,hm.leadingCoeff,map_one,one_mul] at eq
  rw [encode_sum]
  simp only [Algebra.smul_def,AdjoinRoot.algebraMap_eq,map_neg,neg_mul,Finset.sum_neg_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun i => AdjoinRoot.of P (P.coeff i) * AdjoinRoot.root P ^ i) P.natDegree]
  exact neg_eq_of_add_eq_zero_left (by simpa only [add_comm] using eq.symm)

theorem encode_step (hm : P.Monic) (x : Word P.natDegree) :
    encode hm (step (fun i => -P.coeff i.val) x) = encode hm x * AdjoinRoot.root P := by
  rw [step,map_sum,encode_sum hm x,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,smul_mul_assoc,←pow_succ]
  split_ifs with h
  · rw [encode_unit hm _ h]
  · have eq : i.val+1=P.natDegree := by have := i.isLt; omega
    rw [encode_modulus hm,eq]

theorem encode_shifts (hm : P.Monic) (x : Word P.natDegree) (n : ℕ) :
    encode hm (shifts (fun i => -P.coeff i.val) x n) = encode hm x * AdjoinRoot.root P^n := by
  induction n with
  | zero => simp [shifts]
  | succ n ih => rw [shifts,encode_step,ih,pow_succ,mul_assoc]

theorem encode_mul (hm : P.Monic) (x y : Word P.natDegree) :
    encode hm (mul (fun i => -P.coeff i.val) x y) = encode hm x * encode hm y := by
  rw [mul,map_sum,encode_sum hm x,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,encode_shifts,smul_mul_assoc,mul_comm (encode hm y)]

theorem encode_power (hm : P.Monic) (hr : 0 < P.natDegree) (x : Word P.natDegree) (n : ℕ) :
    encode hm (power (fun i => -P.coeff i.val) x n) = encode hm x ^ n := by
  induction n with
  | zero => rw [power,encode_unit hm _ hr,pow_zero,pow_zero]
  | succ n ih => rw [power,encode_mul,ih,pow_succ]

/-- Evaluate an extension-coefficient polynomial supplied in increasing degree order. -/
def evaluate {r : ℕ} (c x : Word r) : List (Word r) → Word r
  | [] => 0
  | a :: tail => a + mul c x (evaluate c x tail)

theorem encode_evaluate (hm : P.Monic) (x : Word P.natDegree) (coeffs : List (Word P.natDegree)) :
    encode hm (evaluate (fun i => -P.coeff i.val) x coeffs) =
      coeffs.foldr (fun a y => encode hm a + encode hm x * y) 0 := by
  induction coeffs with
  | nil => simp [evaluate]
  | cons a tail ih => simp only [evaluate,map_add,encode_mul,ih,List.foldr_cons]

#print axioms encode_evaluate
#print axioms encode_mul
#print axioms encode_power
end ExactPlaneBinaryArithmetic
