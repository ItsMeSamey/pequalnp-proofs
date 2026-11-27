import ExactPlaneWedgeCodec
import ExactPlaneWedgeJoinCharges
namespace ExactPlaneWedgeCodeCharges
open ExactPlaneWedgeCodec ExactPlaneNumericalRows

theorem length_codes (r : Nat) : (codes r).length = 2^(4*r) := by
  simp [codes, List.length_flatMap, length_words, List.sum_replicate, show 4*r=r+(r+(r+r)) by omega, pow_add,
    Nat.mul_assoc]

theorem word_triples (a b c w : Nat) (ha : a≤w) (hb : b≤w) (hc : c≤w) :
    (words a).length*((words b).length*(words c).length) ≤ 2^(3*w) := by
  simp only [length_words,←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem predicate_visits (a b c w : Nat) (ha : a≤w) (hb : b≤w) (hc : c≤w) :
    ((codes c).length*((codes a).length*(codes b).length)) *
      ((words a).length*((words b).length*(words c).length)) ≤ 2^(15*w) := by
  simp only [length_codes,length_words,←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)
#print axioms predicate_visits
end ExactPlaneWedgeCodeCharges
