import Q0FactorActual

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

/-- Slot zero of a gate pair retains the projected value of the gate, including for a
source. Slot one denotes symbolic true without adding a physical gate. Each *pin* can
choose independently between the two, allowing selected uses of a shared source to
remain physical. The pin choices may be different on two inputs of the same OR. -/
structure Cuts where
  «omit» : ℕ → Bool
  bypass : ℕ → Fin 2 → Bool

def normalSlot (n w : ℕ) := if w < n then w else n + 2*(w-n)

def pinSlot (n : ℕ) (p : Cuts) (j : ℕ) (b : Fin 2) (w : ℕ) :=
  normalSlot n w + (if w < n then 0 else if p.bypass j b then 1 else 0)

def marker : Row := ⟨.cleanOr,0,0⟩

noncomputable def projectedRow (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) : Row :=
  ⟨if p.omit j then .cleanOr else if (gateAt C j).op = .and then .product else .disjunction,
    pinSlot n p j 0 (opnd C j 0), pinSlot n p j 1 (opnd C j 1)⟩

noncomputable def rows (n : ℕ) (C : Circuit) (p : Cuts) : ℕ → List Row
  | 0 => []
  | k+1 => rows n C p k ++ [projectedRow n C p k, marker]

noncomputable def layout (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) : Layout n :=
  (rows n C p k).foldl next (seed n)

noncomputable def physicalSlot (n : ℕ) (C : Circuit) (p : Cuts) (k w : ℕ) : Option (Signal n) :=
  readPin (layout n C p k) (normalSlot n w)

theorem compiled_rows (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    ∃ B : Bank n, Trace n B (expense (seed n) (rows n C p k)) ∧
      ∀ w, physically B (physicalSlot n C p k w) := by
  obtain ⟨B,tr,good⟩ := compile (n:=n) (rows n C p k)
  exact ⟨B,tr,fun w => read_good good (normalSlot n w)⟩

theorem layout_succ (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    layout n C p (k+1) = next (next (layout n C p k) (projectedRow n C p k)) marker := by
  simp [layout, rows, List.foldl_append]

private theorem next_length {n : ℕ} (s : Layout n) (r : Row) :
    (next s r).slots.length = s.slots.length + 1 := by
  rcases r with ⟨kind,l,r⟩
  cases kind <;> simp [next]

theorem layout_length (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    (layout n C p k).slots.length = n + 2*k := by
  induction k with
  | zero => simp [layout, rows, seed]
  | succ k ih => rw [layout_succ, next_length, next_length, ih]; omega

private theorem stable {n : ℕ} (s : Layout n) (r : Row) {w : ℕ} (h : w < s.slots.length) :
    readPin (next s r) w = readPin s w := by
  rcases r with ⟨kind,l,r⟩
  cases kind <;> simp [readPin, next, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem stable_pair (n : ℕ) (C : Circuit) (p : Cuts) (k w : ℕ) (h : w < n+2*k) :
    readPin (layout n C p (k+1)) w = readPin (layout n C p k) w := by
  rw [layout_succ, stable _ _ (by rw [next_length,layout_length]; omega),
    stable _ _ (by rwa [layout_length])]

theorem marker_none (n : ℕ) (C : Circuit) (p : Cuts) {i k : ℕ} (h : i < k) :
    readPin (layout n C p k) (n+2*i+1) = none := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases earlier : i < k
    · rw [stable_pair _ _ _ _ _ (by omega)]
      exact ih earlier
    · have eq : i = k := by omega
      subst i
      rw [layout_succ]
      have len := next_length (layout n C p k) (projectedRow n C p k)
      rw [layout_length] at len
      rw [←len]
      simp [readPin, next, marker, List.getD_eq_getElem?_getD]

theorem operand_bound {n k w : ℕ} (p : Cuts) (b : Fin 2) (h : w < n+k) :
    pinSlot n p k b w < n + 2*k := by
  simp only [pinSlot, normalSlot]
  split_ifs <;> omega

theorem pin_none_of_cut {n : ℕ} (C : Circuit) (p : Cuts) {j i : ℕ} (b : Fin 2)
    (h : i < j) (cut : p.bypass j b = true) :
    readPin (layout n C p j) (pinSlot n p j b (n+i)) = none := by
  simpa [pinSlot, normalSlot, Nat.not_lt.mpr (Nat.le_add_right n i),cut] using marker_none n C p h

private theorem expense_append {n : ℕ} (a b : List Row) (s : Layout n) :
    expense s (a ++ b) = expense s a + expense (a.foldl next s) b := by
  induction a generalizing s with
  | nil => simp [expense]
  | cons r rs ih => simp [expense, ih, Nat.add_assoc]

theorem expense_succ (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    expense (seed n) (rows n C p (k+1)) =
    expense (seed n) (rows n C p k) + price (layout n C p k) (projectedRow n C p k) := by
  simp [rows, expense_append, layout, expense, marker, price]

theorem price_zero_of_bypass {n : ℕ} (C : Circuit) (p : Cuts) {j i : ℕ} (h : i < j)
    (b : Fin 2) (cut : p.bypass j b = true) (operand : opnd C j b = n+i) :
    price (layout n C p j) (projectedRow n C p j) = 0 := by
  unfold price
  split
  · rfl
  · apply direct_cost
    fin_cases b
    · change opnd C j 0 = n+i at operand
      change p.bypass j 0 = true at cut
      left
      change readPin _ (pinSlot n p j 0 (opnd C j 0)) = none
      rw [operand]
      exact pin_none_of_cut C p 0 h cut
    · change opnd C j 1 = n+i at operand
      change p.bypass j 1 = true at cut
      right
      change readPin _ (pinSlot n p j 1 (opnd C j 1)) = none
      rw [operand]
      exact pin_none_of_cut C p 1 h cut

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
