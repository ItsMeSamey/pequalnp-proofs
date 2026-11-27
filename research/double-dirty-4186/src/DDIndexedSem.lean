import DDFactorAgreement
import DDIndexedPack
import DDIndexedShape
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

def actualC (n : ℕ) (C : Circuit) (p : Cuts) (K : ℕ) : Circuit := ⟨(build n C p K).gates,0⟩

def actualVal {n : ℕ} (D : Circuit) (x : Fin n → Bool) : Ref → Bool
  | none => true
  | some t => W n D x t.2

private theorem pin_value {n j : ℕ} (C D : Circuit) (p : Cuts) (x : Fin n → Bool) (b : Fin 2)
    (ih : ∀ w < n+j, actualVal D x (ref (build n C p j) w) = denotation (physicalSlot n C p j w) x)
    (bound : opnd C j b < n+j) :
    actualVal D x (pin (build n C p j) n C p j b) =
    denotation (readPin (layout n C p j) (pinSlot n p j b (opnd C j b))) x := by
  by_cases h : n ≤ opnd C j b ∧ p.bypass j b = true
  · have eq : opnd C j b = n+(opnd C j b-n) := by omega
    have hb := pin_none_of_cut (n:=n) C p (i:=opnd C j b-n) b (by omega) h.2
    rw [←eq] at hb
    simp [pin,h,hb,actualVal,denotation]
  · have adr : pinSlot n p j b (opnd C j b) = normalSlot n (opnd C j b) := by
      unfold pinSlot
      split_ifs <;> simp_all <;> omega
    simpa only [pin,if_neg h,adr,physicalSlot] using ih _ bound

private theorem pin_wire_bound {n j : ℕ} {C : Circuit} {p : Cuts} {a : Origin × ℕ}
    {b : Fin 2} (h : pin (build n C p j) n C p j b = some a) : a.2 < n+rank n C p j := by
  simp only [pin] at h
  split at h
  · contradiction
  · rcases a with ⟨o,v⟩
    exact ref_bound h

theorem binary_value {n j K : ℕ} (C : Circuit) (p : Cuts) (ao : IsAO2 n C)
    (hj : j < K) (hk : K ≤ C.gates.length) (x : Fin n → Bool) (skip : p.omit j = false)
    {a b : Origin × ℕ} (l : pin (build n C p j) n C p j 0 = some a)
    (r : pin (build n C p j) n C p j 1 = some b) :
    let D := actualC n C p K
    W n D x (n+rank n C p j) = if (gateAt C j).op = .and then
      W n D x a.2 && W n D x b.2 else W n D x a.2 || W n D x b.2 := by
  let D := actualC n C p K
  have hget := ordered_reader C p hj skip l r
  have hgate : gateAt D (rank n C p j) = ⟨(gateAt C j).op,[a.2,b.2]⟩ := by
    change (build n C p K).gates.getD _ _ = _
    simp only [List.getD_eq_getElem?_getD,hget,Option.getD_some]
  have insj : ins n C p j = some ⟨(gateAt C j).op,[a.2,b.2]⟩ := by simp [ins,l,r,skip,instruction]
  have lt : rank n C p j < D.gates.length := paid_strict C p insj hj
  have ops := (AO_of_IsAO2 n C ao j (by omega)).1
  rcases ops with op | op
  · simpa [op] using W_and n D x _ lt (by rw [hgate]; exact op) _ _ (by rw [hgate]) (pin_wire_bound l) (pin_wire_bound r)
  · simpa [op] using W_or n D x _ lt (by rw [hgate]; exact op) _ _ (by rw [hgate]) (pin_wire_bound l) (pin_wire_bound r)

theorem slot_value {n K : ℕ} (C : Circuit) (p : Cuts) (ao : IsAO2 n C)
    (hK : K ≤ C.gates.length) (x : Fin n → Bool) (k : ℕ) (hk : k ≤ K) :
    ∀ w < n+k, actualVal (actualC n C p K) x (ref (build n C p k) w) =
      denotation (physicalSlot n C p k w) x := by
  let D := actualC n C p K
  induction k with
  | zero =>
    intro w hw
    have h : w < n := by omega
    simp [ref,build,initial,physicalSlot,layout,rows,seed,normalSlot,h,readPin,
      List.getD_eq_getElem?_getD,actualVal,denotation,W_input _ _ _ _ h]
  | succ j ih =>
    intro w hw
    by_cases old : w < n+j
    · rw [stable_ref C p old]
      unfold physicalSlot
      rw [stable_pair n C p j _ (by unfold normalSlot; split <;> omega)]
      exact ih (by omega) w old
    have eq : w = n+j := by omega
    subst w
    rw [row_ref C p (Nat.lt_succ_self j),indexed_recent]
    have L := pin_value C D p x 0 (ih (by omega)) (indexed_op_bound ao (by omega) 0)
    have R := pin_value C D p x 1 (ih (by omega)) (indexed_op_bound ao (by omega) 1)
    cases ho : p.omit j with
    | true => simp [ho,dest,projectedResult,projectedRow,actualVal,denotation]
    | false =>
      have phys (a b : Origin × ℕ)
          (ha : pin (build n C p j) n C p j 0 = some a)
          (hb : pin (build n C p j) n C p j 1 = some b) :=
        binary_value C p ao (show j < K by omega) hK x ho ha hb
      by_cases hand : (gateAt C j).op = .and
      · simp only [projectedResult,projectedRow,ho,Bool.false_eq_true,if_false,hand,if_true,projected_value]
        rw [←L,←R]
        cases hl : pin (build n C p j) n C p j 0 <;> cases hr : pin (build n C p j) n C p j 1 <;>
          simp [actualVal,dest,hand,Option.orElse,D] <;>
          simpa [hand,D] using phys _ _ hl hr
      · simp only [projectedResult,projectedRow,ho,Bool.false_eq_true,if_false,hand,or_project_value]
        rw [←L,←R]
        cases hl : pin (build n C p j) n C p j 0 <;> cases hr : pin (build n C p j) n C p j 1 <;>
          simp [actualVal,dest,hand,Option.orElse,D] <;>
          simpa [hand,D] using phys _ _ hl hr
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
