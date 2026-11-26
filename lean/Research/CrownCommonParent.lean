import Research.CrownCollisionLimit

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem keep_wire (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ((Circuit.mk gs 0).wires w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).getD a false = _
    rw [ih _ (by rw [advance_len]; omega),getD_advance_lt _ _ _ ha]

private theorem step_meet (g : Gate) (x y z : List Bool) (hx : x.length = z.length)
    (hy : y.length = z.length) (ao : g.op = .and ∨ g.op = .or)
    (noncoinc : (isOrGate g && gateBool g x) = true → (isOrGate g && gateBool g y) ≠ true)
    (meet : ∀ v, x.getD v false = true → y.getD v false = true → z.getD v false = true) :
    ∀ v, (advance g x).getD v false = true → (advance g y).getD v false = true →
      (advance g z).getD v false = true := by
  intro v
  by_cases hv : v < z.length
  · simpa only [getD_advance_lt g x v (by omega),getD_advance_lt g y v (by omega),
      getD_advance_lt g z v hv] using meet v
  by_cases zv : v = z.length
  · subst v
    have ex := getD_advance_eq g x
    have ey := getD_advance_eq g y
    rw [hx] at ex
    rw [hy] at ey
    rw [ex,ey,getD_advance_eq]
    rcases ao with hand|hor
    · simp only [hand,GateOp.eval,List.all_map,List.all_eq_true]
      exact fun ax ay i hi => meet i (ax i hi) (ay i hi)
    · intro ax ay
      exact False.elim ((noncoinc (by simpa [isOrGate,hor,gateBool] using ax))
        (by simpa [isOrGate,hor,gateBool] using ay))
  · rw [getD_missing (by rw [advance_len,hx]; omega : (advance g x).length ≤ v)]
    simp

private theorem quiet_prefix_meet (gs : List Gate) (x y z : List Bool) (hx : x.length = z.length)
    (hy : y.length = z.length) (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (meet : ∀ v, x.getD v false = true → y.getD v false = true → z.getD v false = true)
    (k : ℕ) (dis : ∀ j < k, (trueOrFlags gs x).getD j false = true →
      (trueOrFlags gs y).getD j false ≠ true)
    (v : ℕ) (read : v ∈ readAt gs x.length k) :
    ((Circuit.mk gs 0).wires x).getD v false = true →
    ((Circuit.mk gs 0).wires y).getD v false = true →
    ((Circuit.mk gs 0).wires z).getD v false = true := by
  induction gs generalizing k x y z with
  | nil => simp [readAt] at read
  | cons g gs ih =>
    cases k with
    | zero =>
      have lt : v < x.length := by
        change v ∈ orReads g x.length at read
        unfold orReads at read
        split at read
        · exact (Finset.mem_filter.mp read).2
        · simp at read
      simpa only [keep_wire (g::gs) x v lt,keep_wire (g::gs) y v (by omega),keep_wire (g::gs) z v (by omega)] using meet v
    | succ k =>
      apply ih (advance g x) (advance g y) (advance g z) (by simp [advance_len,hx]) (by simp [advance_len,hy])
        (fun q hq => mono q (List.mem_cons_of_mem _ hq))
        (step_meet g x y z hx hy (mono g (by simp)) (dis 0 (Nat.zero_lt_succ _)) meet) k
        (fun j hj => dis (j+1) (by omega))
      simpa only [readAt,advance_len] using read

private theorem zflags (L : List Bool) (h : L.count true = 0) (i : Nat) : L.getD i false = false := by
  induction L generalizing i with
  | nil => simp
  | cons a t ih =>
    cases a with
    | true => simp at h
    | false => cases i with
               | zero => rfl
               | succ i => exact ih (by simpa using h) i

private theorem raw_unique {n : ℕ} (i j : Fin n) (k : ℕ)
    (x : (oneEach i i).getD k false = true) (y : (oneEach j j).getD k false = true) : i=j := by
  by_cases hlt : k<n
  · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,hlt] at x y
    exact x.symm.trans y
  · by_cases hb : k-n<n
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt hlt,hb] at x y
      exact x.symm.trans y
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt hlt,hb] at x

/-- Two distinct diagonals that activate the same parent of an OR gate
also activate a common strictly earlier OR gate. -/
theorem crown_common_parent (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (i j : Fin 12) (ne : i ≠ j) (k : Fin C.gates.length)
    (a : ℕ) (read : a ∈ readAt C.gates 24 k.val)
    (ax : (C.wires (oneEach i i)).getD a false = true)
    (ay : (C.wires (oneEach j j)).getD a false = true) :
    ∃ e : Fin C.gates.length, e < k ∧ e ∈ activeOrIds C.gates (oneEach i i) ∧
      e ∈ activeOrIds C.gates (oneEach j j) := by
  classical
  let x := oneEach i i
  let y := oneEach j j
  let z := List.replicate 24 false
  have xl : x.length = 24 := by simp [x,oneEach]
  have yl : y.length = 24 := by simp [y,oneEach]
  have zl : z.length = 24 := by simp [z]
  have raw (k : ℕ) (hx : x.getD k false = true) (hy : y.getD k false = true) : z.getD k false = true :=
    False.elim (ne (raw_unique i j k hx hy))
  by_contra H
  have dis (e : ℕ) (he : e < k.val) (ex : (trueOrFlags C.gates x).getD e false = true)
      (ey : (trueOrFlags C.gates y).getD e false = true) : False := by
    let f : Fin C.gates.length := ⟨e,he.trans k.isLt⟩
    exact H ⟨f,he,(activeOrIds_mem _ _ f).mpr ex,(activeOrIds_mem _ _ f).mpr ey⟩
  have val := quiet_prefix_meet C.gates x y z (by omega) (by omega)
    (fun g hg => (hm g hg).1) raw k.val dis a (by simpa only [xl] using read) ax ay
  have on : (trueOrFlags C.gates z).getD k.val false = true :=
    (flag_iff_final_parent _ _ _).mpr ⟨a,by simpa only [zl] using read,val⟩
  rw [zflags _ (crown_allzero_no_or C hm rep size ors)] at on
  contradiction

end PEqualNP.Research.MissingCell
