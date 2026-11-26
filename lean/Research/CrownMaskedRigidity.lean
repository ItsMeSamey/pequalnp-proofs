import Research.CrownFirstTrigger

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- A masked-true wire depends entirely on AND gates and primary wires.
Restoring every OR leaves this wire's value unchanged on every input. -/
private theorem mask_rigidity_aux (gs : List Gate) (w x y : List Bool) (lx : x.length=w.length)
    (ly : y.length=w.length) (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (agree : ∀ a, w.getD a false = true → x.getD a false = y.getD a false) (a : ℕ)
    (witness : (maskedWires gs w).getD a false = true) :
    (maskedWires gs x).getD a false = ((Circuit.mk gs 0).wires y).getD a false := by
  induction gs generalizing w x y with
  | nil => exact agree a witness
  | cons g gs ih =>
    apply ih (advance (maskGate g) w) (advance (maskGate g) x) (advance g y)
      (by simp [advance_len,lx]) (by simp [advance_len,ly]) (fun b h => mono b (List.mem_cons_of_mem _ h)) _ witness
    intro b
    by_cases lt : b<w.length
    · simpa only [getD_advance_lt _ _ _ lt,getD_advance_lt (maskGate g) x b (by omega),
        getD_advance_lt g y b (by omega)] using agree b
    · by_cases eq : b=w.length
      · subst b
        have ex := getD_advance_eq (maskGate g) x
        have ey := getD_advance_eq g y
        rw [lx] at ex
        rw [ly] at ey
        rw [getD_advance_eq,ex,ey]
        rcases mono g (List.mem_cons_self ..) with hand | hor
        · have em : maskGate g = g := by simp [maskGate,isOrGate,hand]
          rw [em]
          intro ht
          have all : ∀ j ∈ g.inputs, w.getD j false = true := by simpa [hand,GateOp.eval] using ht
          congr 1
          apply List.map_congr_left
          intro j hj
          exact agree j (all j hj)
        · simp [maskGate,isOrGate,hor,GateOp.eval]
      · rw [getD_missing (by rw [advance_len];omega : (advance (maskGate g) w).length ≤ b)]
        simp

theorem masked_true_wire_rigid (gs : List Gate) (w y : List Bool) (len : y.length=w.length)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (a : ℕ)
    (witness : (maskedWires gs w).getD a false = true) :
    (maskedWires gs y).getD a false = ((Circuit.mk gs 0).wires y).getD a false :=
  mask_rigidity_aux gs w y y len len mono (fun _ _ => rfl) a witness

theorem trigger_unique_on_actual_diagonals {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (a : ℕ) (i j : Fin n)
    (witness : (maskedWires C.gates (oneEach i i)).getD a false = true)
    (zero : (maskedWires C.gates (List.replicate (n+n) false)).getD a false = false)
    (other : (C.wires (oneEach j j)).getD a false = true) : i=j := by
  have eq := masked_true_wire_rigid C.gates (oneEach i i) (oneEach j j) (by simp [oneEach])
    (fun g hg => (hm g hg).1) a witness
  exact masked_unique_diagonal C hm a zero i j witness (eq.trans other)

end PEqualNP.Research.MissingCell
