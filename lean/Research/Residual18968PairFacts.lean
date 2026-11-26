import Std

set_option maxRecDepth 50000
set_option exponentiation.threshold 1000
set_option maxHeartbeats 0

namespace Residual18968

/-- Decimal seed chunks and lane rotation from the 26 fixed input columns. -/
def unpack (chunks : List Nat) := chunks.foldl (fun n x => 10^19*n + x) 0
def pointSeed := unpack [9820805366576, 3697915243686326406, 3772072151941599339, 8659025085589474860, 762494670591627578, 9998186360218198862, 7813898889586405971, 2492579563743896212, 8260024526693886294, 9773907680645894422, 2402781631192498177]
def lineSeed := unpack [1231427982286, 4772337669408815584, 1455263899191340963, 9832454934276868335, 925941497934626908, 2690850975655642988, 2184208476895364767, 3353807136187280627, 2669759675931372401, 6826416250394358953, 6258748122593763329]
def rotate (seed shift : Nat) :=
  let lanes := (2^676-1)/8191
  (seed >>> (13-shift) &&& ((2^shift-1)*lanes)) |||
    (seed <<< shift &&& ((8192-2^shift)*lanes))
def point (p : Fin 13) := rotate pointSeed p.val
def line (t : Fin 7) := rotate lineSeed (6+t.val)
/-- Negative rows among the low 676 bits, from the fixed output at wire 88. -/
def negative := (2^676-1 : Nat) - 4503599627370495
def incident (t : Fin 7) (p : Fin 13) : Bool :=
  [0,1,3,9].any fun d : Nat => (6+t.val+d)%13 == p.val
def meets (u : Fin 7) : Nat :=
  (List.finRange 13).foldl (fun acc p => if incident u p then acc ||| point p else acc) 0

/-- Nonempty intersection of the masks means at least one common negative row. -/
theorem zeroLinePairs : ∀ a b : Fin 13, a ≤ b →
    negative &&& point a &&& point b ≠ 0 := by decide +kernel

theorem outsidePairExtensions : ∀ t u : Fin 7, t ≠ u → ∀ a b : Fin 13,
    a < b → incident t a = false → incident t b = false →
    negative &&& line t &&& point a &&& point b &&& meets u ≠ 0 := by decide +kernel

private theorem rowBound {i : Nat} (h : negative.testBit i = true) : i < 676 := by
  apply Nat.lt_of_not_ge
  intro hi
  have small : negative < 2^676 := by decide +kernel
  exact (Nat.not_le_of_gt small)
    (Nat.le_trans (Nat.pow_le_pow_right Nat.zero_lt_two hi) (Nat.ge_two_pow_of_testBit h))

theorem zeroLineWitness (a b : Fin 13) (hab : a ≤ b) :
    ∃ i : Fin 676, negative.testBit i ∧ (point a).testBit i ∧ (point b).testBit i := by
  obtain ⟨i, h⟩ := Nat.exists_testBit_of_ne_zero (zeroLinePairs a b hab)
  simp only [Nat.testBit_and, Bool.and_eq_true] at h
  exact ⟨⟨i, rowBound h.1.1⟩, h.1.1, h.1.2, h.2⟩

private theorem hitMember (u : Fin 7) (i : Nat) (xs : List (Fin 13)) (acc : Nat)
    (h : (xs.foldl (fun v p => if incident u p then v ||| point p else v) acc).testBit i) :
    acc.testBit i ∨ ∃ p : Fin 13, incident u p ∧ (point p).testBit i := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons x xs ih =>
    rcases ih _ h with h | h
    · by_cases hx : incident u x
      · simp only [hx, ite_true, Nat.testBit_or, Bool.or_eq_true] at h
        exact h.elim Or.inl (fun h => Or.inr ⟨x, hx, h⟩)
      · exact Or.inl (by simpa [hx] using h)
    · exact Or.inr h

theorem extensionWitness (t u : Fin 7) (htu : t ≠ u) (a b : Fin 13) (hab : a < b)
    (ha : incident t a = false) (hb : incident t b = false) :
    ∃ i : Fin 676, negative.testBit i ∧ (line t).testBit i ∧ (point a).testBit i ∧
      (point b).testBit i ∧ ∃ p : Fin 13, incident u p ∧ (point p).testBit i := by
  obtain ⟨i, h⟩ := Nat.exists_testBit_of_ne_zero (outsidePairExtensions t u htu a b hab ha hb)
  simp only [Nat.testBit_and, Bool.and_eq_true] at h
  have chosen := hitMember u i (List.finRange 13) 0 h.2
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at chosen
  exact ⟨⟨i, rowBound h.1.1.1.1⟩, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, chosen⟩

end Residual18968

theorem Residual18968.negativeRow : ∀ i : Fin 676,
    Residual18968.negative.testBit i = !((4503599627370495 : Nat).testBit i) := by decide +kernel

#print axioms Residual18968.zeroLineWitness
#print axioms Residual18968.extensionWitness
#print axioms Residual18968.negativeRow
