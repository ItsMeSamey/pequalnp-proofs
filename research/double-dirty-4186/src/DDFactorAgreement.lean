import DDPhysicalRows

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem or_project_value {n : ℕ} (a b : Option (Signal n)) (x : Fin n → Bool) :
    denotation (projectedOr a b) x = (denotation a x || denotation b x) := by
  cases a <;> cases b <;> simp [projectedOr, denotation, join]

private def result {n : ℕ} (s : Layout n) (r : Row) :=
  match r.kind with
  | .source | .cleanOr => none
  | .product => project (readPin s r.left) (readPin s r.right)
  | .disjunction => projectedOr (readPin s r.left) (readPin s r.right)

private theorem get_result {n : ℕ} (s : Layout n) (r : Row) :
    readPin (next s r) s.slots.length = result s r := by
  rcases r with ⟨kind,l,r⟩
  cases kind <;> simp [readPin, next, result, List.getD_eq_getElem?_getD]

private theorem mostRecent (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) :
    physicalSlot n C p (j+1) (n+j) = result (layout n C p j) (projectedRow n C p j) := by
  unfold physicalSlot
  rw [layout_succ]
  have adr : normalSlot n (n+j) = n+2*j := by simp [normalSlot, Nat.not_lt.mpr (Nat.le_add_right ..)]
  rw [adr, ←layout_length n C p j]
  let s := layout n C p j
  let r := projectedRow n C p j
  change readPin (next (next s r) marker) s.slots.length = result s r
  have lt : s.slots.length < (next s r).slots.length := by
    generalize r = rr
    rcases rr with ⟨kind,l,rr⟩
    cases kind <;> simp [next]
  change (((next s r).slots ++ [none]).getD s.slots.length none) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left lt]
  exact get_result s r

/-- Wires that matter to this output on this assignment. A bypassed pin must already
be true. Other pins trace back through the original circuit. -/
structure Safe {n : ℕ} (C : Circuit) (p : Cuts) (x : Fin n → Bool) (need : ℕ → Prop) : Prop where
  omitted : ∀ j < C.gates.length, need (n+j) → p.omit j = true → W n C x (n+j) = true
  pin : ∀ j < C.gates.length, need (n+j) → p.omit j = false → ∀ b : Fin 2,
    if n ≤ opnd C j b ∧ p.bypass j b = true then W n C x (opnd C j b) = true
    else need (opnd C j b)

theorem agree {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (p : Cuts) (x : Fin n → Bool)
    (need : ℕ → Prop) (ok : Safe C p x need) (k : ℕ) (hk : k ≤ C.gates.length) :
    ∀ w < n+k, need w → W n C x w = denotation (physicalSlot n C p k w) x := by
  induction k with
  | zero =>
    intro w bound _
    have hw : w < n := by omega
    rw [W_input n C x w hw]
    simp [physicalSlot,layout,rows,seed,normalSlot,hw,readPin,List.getD_eq_getElem?_getD,denotation]
  | succ j ih =>
    intro w bound want
    have hj : j < C.gates.length := by omega
    by_cases prev : w < n+j
    · change W n C x w = denotation (readPin _ _) x
      rw [stable_pair _ _ _ _ _ (by unfold normalSlot; split <;> omega)]
      exact ih (by omega) w prev want
    have eq : w = n+j := by omega
    subst w
    rw [mostRecent]
    cases omitted : p.omit j with
    | true =>
      simpa [projectedRow,result,omitted,denotation] using ok.omitted j hj want omitted
    | false =>
      obtain ⟨ops,a,b,pins,ha,hb⟩ := AO_of_IsAO2 n C ao j hj
      have ap : opnd C j 0 = a := by simp [opnd,pins]
      have bp : opnd C j 1 = b := by simp [opnd,pins]
      have pinEq (d : Fin 2) (boundPin : opnd C j d < n+j) :
          W n C x (opnd C j d) =
            denotation (readPin (layout n C p j) (pinSlot n p j d (opnd C j d))) x := by
        have rule := ok.pin j hj want omitted d
        by_cases cut : n ≤ opnd C j d ∧ p.bypass j d = true
        · rw [if_pos cut] at rule
          have sub : opnd C j d = n + (opnd C j d-n) := by omega
          have wire := pin_none_of_cut (n:=n) C p (i:=opnd C j d-n) d (by omega) cut.2
          rw [←sub] at wire
          rw [wire]
          exact rule
        · rw [if_neg cut] at rule
          have adr : pinSlot n p j d (opnd C j d) = normalSlot n (opnd C j d) := by
            unfold pinSlot
            split_ifs <;> simp_all <;> omega
          rw [adr]
          exact ih (by omega) _ boundPin rule
      have va := pinEq 0 (by simpa only [ap] using ha)
      have vb := pinEq 1 (by simpa only [bp] using hb)
      rw [ap] at va
      rw [bp] at vb
      rcases ops with op | op
      · simpa [projectedRow,result,omitted,op,ap,bp,projected_value,←va,←vb] using
          W_and n C x j hj op a b pins ha hb
      · simpa [projectedRow,result,omitted,op,ap,bp,or_project_value,←va,←vb] using
          W_or n C x j hj op a b pins ha hb

theorem restore_root {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (p : Cuts) (h : Signal n)
    (w : ℕ) (bound : w < n+C.gates.length)
    (implies : ∀ x, W n C x w = true → h x = true)
    (whenOn : ∀ x, h x = true → ∃ need, need w ∧ Safe C p x need) (x : Fin n → Bool) :
    W n C x w = (h x && denotation (physicalSlot n C p C.gates.length w) x) := by
  cases hx : h x with
  | false => cases hw : W n C x w <;> simp_all
  | true =>
    obtain ⟨need,hn,hs⟩ := whenOn x hx
    simpa using agree C ao p x need hs C.gates.length le_rfl w bound hn

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
