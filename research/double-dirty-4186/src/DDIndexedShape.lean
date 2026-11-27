import DDIndexedRows

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

def projectedResult {n : ℕ} (s : Layout n) (r : Row) :=
  match r.kind with
  | .source | .cleanOr => none
  | .product => project (readPin s r.left) (readPin s r.right)
  | .disjunction => projectedOr (readPin s r.left) (readPin s r.right)

private theorem get_result {n : ℕ} (s : Layout n) (r : Row) :
    readPin (next s r) s.slots.length = projectedResult s r := by
  rcases r with ⟨kind,l,r⟩
  cases kind <;> simp [readPin, next, projectedResult, List.getD_eq_getElem?_getD]

theorem indexed_recent (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) :
    physicalSlot n C p (j+1) (n+j) = projectedResult (layout n C p j) (projectedRow n C p j) := by
  unfold physicalSlot
  rw [layout_succ]
  have adr : normalSlot n (n+j) = n+2*j := by simp [normalSlot, Nat.not_lt.mpr (Nat.le_add_right ..)]
  rw [adr, ←layout_length n C p j]
  let s := layout n C p j
  let r := projectedRow n C p j
  change readPin (next (next s r) marker) s.slots.length = projectedResult s r
  have lt : s.slots.length < (next s r).slots.length := by
    generalize r = rr
    rcases rr with ⟨kind,l,rr⟩
    cases kind <;> simp [next]
  change ((next s r).slots ++ [none]).getD s.slots.length none = projectedResult s r
  rw [List.getD_append _ _ _ _ lt]
  exact get_result s r

private theorem pin_match {n j : ℕ} (C : Circuit) (p : Cuts) (b : Fin 2)
    (ih : ∀ w < n+j, (ref (build n C p j) w).isSome = (physicalSlot n C p j w).isSome)
    (bound : opnd C j b < n+j) :
    (pin (build n C p j) n C p j b).isSome =
    (readPin (layout n C p j) (pinSlot n p j b (opnd C j b))).isSome := by
  by_cases h : n ≤ opnd C j b ∧ p.bypass j b = true
  · have eq : opnd C j b = n+(opnd C j b-n) := by omega
    have hb := pin_none_of_cut (n:=n) C p (i:=opnd C j b-n) b (by omega) h.2
    rw [←eq] at hb
    simp [pin,h,hb]
  · have adr : pinSlot n p j b (opnd C j b) = normalSlot n (opnd C j b) := by
      unfold pinSlot
      split_ifs <;> simp_all <;> omega
    simpa only [pin,if_neg h,adr,physicalSlot] using ih _ bound

theorem indexed_op_bound {n : ℕ} {C : Circuit} (ao : IsAO2 n C)
    {j : ℕ} (h : j < C.gates.length) (b : Fin 2) : opnd C j b < n+j := by
  obtain ⟨_,a,c,pins,ha,hc⟩ := AO_of_IsAO2 n C ao j h
  fin_cases b <;> simp [opnd,pins,ha,hc]

theorem shape {n : ℕ} (C : Circuit) (p : Cuts) (ao : IsAO2 n C)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    ∀ w < n+k, (ref (build n C p k) w).isSome = (physicalSlot n C p k w).isSome := by
  induction k with
  | zero =>
    intro w hw
    have h : w < n := by omega
    simp [ref,build,initial,physicalSlot,layout,rows,seed,normalSlot,h,readPin,List.getD_eq_getElem?_getD]
  | succ j ih =>
    intro w hw
    by_cases old : w < n+j
    · rw [stable_ref C p old]
      change _ = (readPin _ _).isSome
      rw [stable_pair n C p j _ (by unfold normalSlot; split <;> omega)]
      exact ih (by omega) w old
    have eq : w = n+j := by omega
    subst w
    rw [row_ref C p (Nat.lt_succ_self j), indexed_recent]
    have L := pin_match C p 0 (ih (by omega)) (indexed_op_bound ao (by omega) 0)
    have R := pin_match C p 1 (ih (by omega)) (indexed_op_bound ao (by omega) 1)
    cases hl : pin (build n C p j) n C p j 0 <;> cases hr : pin (build n C p j) n C p j 1 <;>
      cases hv : readPin (layout n C p j) (pinSlot n p j 0 (opnd C j 0)) <;>
      cases hu : readPin (layout n C p j) (pinSlot n p j 1 (opnd C j 1)) <;>
      cases ho : p.omit j <;> by_cases hand : (gateAt C j).op = .and <;>
      simp_all [projectedResult,projectedRow,dest,project,projectedOr,Option.orElse]
theorem rank_expense {n : ℕ} (C : Circuit) (p : Cuts) (ao : IsAO2 n C)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    rank n C p k = expense (seed n) (rows n C p k) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    change (build n C p (j+1)).gates.length = _
    rw [gates_step,List.length_append,expense_succ,←ih (by omega)]
    congr 1
    have L := pin_match C p 0 (shape C p ao j (by omega)) (indexed_op_bound ao (by omega) 0)
    have R := pin_match C p 1 (shape C p ao j (by omega)) (indexed_op_bound ao (by omega) 1)
    unfold ins
    cases hl : pin (build n C p j) n C p j 0 <;> cases hr : pin (build n C p j) n C p j 1 <;>
      cases hv : readPin (layout n C p j) (pinSlot n p j 0 (opnd C j 0)) <;>
      cases hu : readPin (layout n C p j) (pinSlot n p j 1 (opnd C j 1)) <;>
      cases ho : p.omit j <;> by_cases hand : (gateAt C j).op = .and <;>
      simp_all [price,projectedRow,instruction,andCost]
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
