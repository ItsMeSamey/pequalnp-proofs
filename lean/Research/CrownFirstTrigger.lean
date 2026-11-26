import Research.CrownIndexedOrReads

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def maskGate (g : Gate) : Gate := if isOrGate g then ⟨.or,[]⟩ else g

def maskedWires : List Gate → List Bool → List Bool
  | [],w => w
  | g::gs,w => maskedWires gs (advance (maskGate g) w)

private theorem masked_old (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    (maskedWires gs w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [maskedWires,ih _ (by rw [advance_len]; omega),getD_advance_lt _ _ _ ha]

private theorem same_when_off (g : Gate) (w : List Bool)
    (off : (isOrGate g && gateBool g w) = false) : advance (maskGate g) w = advance g w := by
  cases ho : isOrGate g with
  | false => simp [maskGate,ho]
  | true =>
    have hg : gateBool g w = false := by simpa only [ho,Bool.true_and] using off
    change w ++ [gateBool (maskGate g) w] = w ++ [gateBool g w]
    rw [hg]
    simp only [maskGate,ho,↓reduceIte]
    rfl

private theorem actual_old (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ((Circuit.mk gs 0).wires w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).getD a false = _
    rw [ih _ (by rw [advance_len]; omega),getD_advance_lt _ _ _ ha]

theorem first_parent_masked (gs : List Gate) (x z : List Bool) (sameLen : x.length = z.length)
    (k : ℕ) (on : (trueOrFlags gs x).getD k false = true)
    (before : ∀ j < k, (trueOrFlags gs x).getD j false = false)
    (zero : ∀ j, (trueOrFlags gs z).getD j false = false)
    (a : ℕ) (ha : a ∈ readAt gs x.length k) (val : ((Circuit.mk gs 0).wires x).getD a false = true) :
    (maskedWires gs x).getD a false = true ∧ (maskedWires gs z).getD a false = false := by
  induction gs generalizing x z k with
  | nil => simp [trueOrFlags] at on
  | cons g gs ih =>
    cases k with
    | zero =>
      change (isOrGate g && gateBool g x) = true at on
      have hor := (Bool.and_eq_true_iff.mp on).1
      have op : g.op = .or := by cases h : g.op <;> simp_all [isOrGate]
      have mem := ha
      simp only [readAt,orReads,hor,↓reduceIte,Finset.mem_filter,List.mem_toFinset] at mem
      have hzero := zero 0
      change (isOrGate g && gateBool g z) = false at hzero
      have base : gateBool g z = false := by simpa only [hor,Bool.true_and] using hzero
      have all : ∀ b ∈ g.inputs, z.getD b false = false := by simpa [gateBool,op,GateOp.eval] using base
      rw [actual_old _ _ _ mem.2] at val
      exact ⟨(masked_old _ _ _ mem.2).trans val,(masked_old _ _ _ (sameLen ▸ mem.2)).trans (all _ mem.1)⟩
    | succ k =>
      have hx := same_when_off g x (before 0 (Nat.zero_lt_succ _))
      have hz := same_when_off g z (zero 0)
      have mem : a ∈ readAt gs (advance g x).length k := by simpa only [readAt,advance_len] using ha
      have next := ih (advance g x) (advance g z) (by simp [advance_len,sameLen]) k on
        (fun j hj => before (j+1) (by omega)) (fun j => zero (j+1)) mem val
      simpa only [maskedWires,hx,hz] using next

theorem first_or_trigger (gs : List Gate) (x z : List Bool) (sameLen : x.length = z.length)
    (k : ℕ) (on : (trueOrFlags gs x).getD k false = true)
    (before : ∀ j < k, (trueOrFlags gs x).getD j false = false)
    (zero : ∀ j, (trueOrFlags gs z).getD j false = false) :
    ∃ a ∈ readAt gs x.length k, (maskedWires gs x).getD a false = true ∧
      (maskedWires gs z).getD a false = false ∧ ((Circuit.mk gs 0).wires x).getD a false = true := by
  induction gs generalizing x z k with
  | nil => simp [trueOrFlags] at on
  | cons g gs ih =>
    cases k with
    | zero =>
      change (isOrGate g && gateBool g x) = true at on
      obtain ⟨hor,hg⟩ := Bool.and_eq_true_iff.mp on
      have op : g.op = .or := by cases h : g.op <;> simp_all [isOrGate]
      have hzero := zero 0
      change (isOrGate g && gateBool g z) = false at hzero
      have base : gateBool g z = false := by simpa only [hor,Bool.true_and] using hzero
      have any : ∃ a ∈ g.inputs, x.getD a false = true := by simpa [gateBool,op,GateOp.eval] using hg
      have all : ∀ a ∈ g.inputs, z.getD a false = false := by simpa [gateBool,op,GateOp.eval] using base
      obtain ⟨a,ha,hx⟩ := any
      have lt : a < x.length := by
        by_contra! bad
        rw [getD_missing bad] at hx
        contradiction
      exact ⟨a,by simp [readAt,orReads,hor,ha,lt],(masked_old _ _ _ lt).trans hx,
        (masked_old _ _ _ (by omega)).trans (all a ha),(actual_old _ _ _ lt).trans hx⟩
    | succ k =>
      have hx := same_when_off g x (before 0 (Nat.zero_lt_succ _))
      have hz := same_when_off g z (zero 0)
      have next := ih (advance g x) (advance g z) (by simp [advance_len,sameLen]) k on
        (fun j hj => before (j+1) (by omega)) (fun j => zero (j+1))
      obtain ⟨a,mem,hit,off,yes⟩ := next
      refine ⟨a,?_,?_,?_,?_⟩
      · simpa only [readAt,advance_len] using mem
      · simpa only [maskedWires,hx] using hit
      · simpa only [maskedWires,hz] using off
      · exact yes

private theorem masked_pair_step (g : Gate) (z x y : List Bool) (hl : x.length = z.length)
    (hr : y.length = z.length) (hop : g.op = .and ∨ g.op = .or)
    (h : ∀ a, x.getD a false = true → y.getD a false = true → z.getD a false = true) :
    ∀ a, (advance (maskGate g) x).getD a false = true →
      (advance (maskGate g) y).getD a false = true → (advance (maskGate g) z).getD a false = true := by
  intro a
  by_cases lt : a < z.length
  · simpa only [getD_advance_lt (maskGate g) z a lt,getD_advance_lt (maskGate g) x a (by omega),
      getD_advance_lt (maskGate g) y a (by omega)] using h a
  · by_cases eq : a = z.length
    · subst a
      have xeq := getD_advance_eq (maskGate g) x
      have yeq := getD_advance_eq (maskGate g) y
      rw [hl] at xeq
      rw [hr] at yeq
      rw [xeq,yeq,getD_advance_eq]
      rcases hop with hop | hop
      · simp only [maskGate,isOrGate,hop,Bool.false_eq_true,↓reduceIte,GateOp.eval,List.all_map,List.all_eq_true]
        exact fun hx hy j hj => h j (hx j hj) (hy j hj)
      · simp [maskGate,isOrGate,hop,GateOp.eval]
    · rw [getD_missing (by rw [advance_len,hl];omega : (advance (maskGate g) x).length ≤ a)]
      simp

private theorem masked_pair (gs : List Gate) (z x y : List Bool) (hl : x.length = z.length)
    (hr : y.length = z.length) (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h : ∀ a, x.getD a false = true → y.getD a false = true → z.getD a false = true) :
    ∀ a, (maskedWires gs x).getD a false = true → (maskedWires gs y).getD a false = true →
      (maskedWires gs z).getD a false = true := by
  induction gs generalizing z x y with
  | nil => exact h
  | cons g gs ih =>
    exact ih _ _ _ (by simp [advance_len,hl]) (by simp [advance_len,hr])
      (fun a ha => mono a (List.mem_cons_of_mem _ ha))
      (masked_pair_step g z x y hl hr (mono g (List.mem_cons_self ..)) h)

theorem masked_unique_diagonal {n : ℕ} (C : Circuit) (hm : Monotone2 C) (a : ℕ)
    (zero : (maskedWires C.gates (List.replicate (n+n) false)).getD a false = false)
    (i j : Fin n) (hi : (maskedWires C.gates (oneEach i i)).getD a false = true)
    (hj : (maskedWires C.gates (oneEach j j)).getD a false = true) : i=j := by
  by_contra ne
  have raw (k : ℕ) (x : (oneEach i i).getD k false = true) (y : (oneEach j j).getD k false = true) :
      (List.replicate (n+n) false).getD k false = true := by
    exfalso
    apply ne
    by_cases hlt : k<n
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,hlt] at x y
      exact x.symm.trans y
    · by_cases hb : k-n<n
      · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt hlt,hb] at x y
        exact x.symm.trans y
      · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt hlt,hb] at x
  have h := masked_pair C.gates _ _ _ (by simp [oneEach]) (by simp [oneEach])
    (fun g hg => (hm g hg).1) raw a hi hj
  rw [zero] at h
  contradiction

private theorem all_off (bs : List Bool) (zero : bs.count true = 0) (j : ℕ) : bs.getD j false = false := by
  induction bs generalizing j with
  | nil => simp
  | cons b bs ih =>
    cases b with
    | false =>
      cases j with
      | zero => rfl
      | succ j => exact ih (by simpa using zero) j
    | true => simp at zero

theorem crown_first_trigger_choice (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (S : Finset (Fin 12)) (pos : ∀ i ∈ S, 0 < (trueOrFlags C.gates (oneEach i i)).count true) :
    ∃ (gate : S → Fin C.gates.length) (wire : S → ℕ), Function.Injective wire ∧
      ∀ i, gate i ∈ activeOrIds C.gates (oneEach i.val i.val) ∧
        (∀ j ∈ activeOrIds C.gates (oneEach i.val i.val), gate i ≤ j) ∧
        wire i ∈ readAt C.gates 24 (gate i).val ∧
        (C.wires (oneEach i.val i.val)).getD (wire i) false = true := by
  classical
  let x (i : S) := oneEach i.val i.val
  let z := List.replicate 24 false
  let A (i : S) := activeOrIds C.gates (x i)
  have nonempty (i : S) : (A i).Nonempty := Finset.card_pos.mp (by
    change 0 < (activeOrIds C.gates (x i)).card
    rw [activeOrIds_card]
    exact pos _ i.property)
  let gate (i : S) := (A i).min' (nonempty i)
  have mem (i : S) : gate i ∈ A i := Finset.min'_mem _ _
  have low (i : S) (j : Fin C.gates.length) (hj : j ∈ A i) : gate i ≤ j := Finset.min'_le _ _ hj
  have hz := crown_allzero_no_or C hm rep size ors
  have zoff (j : ℕ) : (trueOrFlags C.gates z).getD j false = false := all_off _ hz j
  have avail (i : S) : ∃ a ∈ readAt C.gates 24 (gate i).val, (maskedWires C.gates (x i)).getD a false = true ∧
      (maskedWires C.gates z).getD a false = false ∧ (C.wires (x i)).getD a false = true := by
    have xl : (x i).length = 24 := by simp [x,oneEach]
    have on := (activeOrIds_mem C.gates (x i) (gate i)).mp (mem i)
    have before (j : ℕ) (hj : j < (gate i).val) : (trueOrFlags C.gates (x i)).getD j false = false := by
      cases hh : (trueOrFlags C.gates (x i)).getD j false with
      | false => rfl
      | true =>
        let f : Fin C.gates.length := ⟨j,hj.trans (gate i).isLt⟩
        have lb := low i f ((activeOrIds_mem _ _ f).mpr hh)
        exact False.elim (Nat.not_le_of_lt hj lb)
    have r := first_or_trigger C.gates (x i) z (by simp [z,xl]) (gate i).val on before zoff
    rw [xl] at r
    exact r
  choose wire hread hmask hzero hactual using avail
  refine ⟨gate,wire,?_,fun i => ⟨mem _,low _,hread _,hactual _⟩⟩
  intro i j hw
  apply Subtype.ext
  exact masked_unique_diagonal C hm (wire i) (hzero i) i.val j.val (hmask i) (hw ▸ hmask j)

end PEqualNP.Research.MissingCell
