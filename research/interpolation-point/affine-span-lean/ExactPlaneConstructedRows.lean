import ExactPlaneWordField
import ExactPlaneFastIrreducibleConstructor
import ExactPlaneEagerField
import Mathlib.Data.Nat.Log
namespace ExactPlaneConstructedRows
open ExactPlaneFieldSampler ExactPlaneSamplerRank ExactPlaneNumericalRows
open ExactPlaneBinaryArithmetic (encode_word power encode_word_power)
open ExactPlaneIrreducibleSearch (construct construct_spec fastConstruct fastConstruct_eq poly)

def exponent (m R : Nat) := Nat.log 2 (m*2^R)+1

theorem band (m R : Nat) (hm : 0<m) :
    m*2^R<2^(exponent m R) ∧ 2^(exponent m R)≤2*(m*2^R) := by
  refine ⟨Nat.lt_pow_succ_log_self (by decide) _,?_⟩
  rw [exponent,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.mul_ne_zero hm.ne' (by positivity)))

theorem word_hits (r m R : Nat) (hr : 0<r) (hm : 0<m) (large : m*2^R<2^r) :
    OntoHits (points (ExactPlaneQuotientRows.seedRows m (construct r))).toFinset R := by
  classical
  let c := construct r
  obtain ⟨_,_,irr⟩ := construct_spec r hr
  letI : Fact (Irreducible (poly c)) := ⟨irr⟩
  let e := encode_word c
  letI : Fintype (AdjoinRoot (poly c)) := Fintype.ofEquiv (V r) e.toEquiv
  letI : Fintype (D (AdjoinRoot (poly c))) := Fintype.ofEquiv (AdjoinRoot (poly c))
    (Module.finBasis F (AdjoinRoot (poly c))).toDualEquiv.toEquiv
  have card : Fintype.card (AdjoinRoot (poly c))=2^r := by
    rw [←Fintype.card_congr e.toEquiv]
    simp [V,F,ZMod.card]
  exact power_hits e (power c) (encode_word_power c hr) hm (by simpa only [card] using large)

def generate : (m R : Nat) → List (Vector F m)
  | 0,_ => zeroRow
  | m+1,R => ExactPlaneEagerField.seedRows (m+1)
      (ExactPlaneEagerField.store (fastConstruct (exponent (m+1) R)))

theorem generate_hits (m R : Nat) : OntoHits (points (generate m R)).toFinset R := by
  cases m with
  | zero => exact ExactPlaneNumericalRows.zero_hits R
  | succ m =>
    simp only [generate,ExactPlaneEagerField.seedRows_eq,ExactPlaneEagerField.read_store]
    rw [fastConstruct_eq (exponent (m+1) R) (by unfold exponent; omega)]
    exact word_hits _ _ _ (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (band _ R (Nat.zero_lt_succ _)).1

theorem generate_count (m R : Nat) : (generate m R).length≤max 1 ((2*(m*2^R))^2) := by
  cases m with
  | zero => simp [generate,zeroRow]
  | succ m =>
    rw [generate,ExactPlaneEagerField.seedRows_eq,ExactPlaneQuotientRows.count]
    exact (Nat.pow_le_pow_left (band _ R (Nat.zero_lt_succ _)).2 2).trans (le_max_right _ _)
#print axioms generate_hits
#print axioms generate_count
end ExactPlaneConstructedRows
