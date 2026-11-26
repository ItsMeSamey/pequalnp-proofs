import Research.CrownIndexedOrValues
import Research.CrownStaticOrIds

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- Replace one gate by a unary AND which copies an earlier wire. -/
def copyOrAt : List Gate → ℕ → ℕ → List Gate
  | [],_,_ => []
  | _::gs,0,a => ⟨.and,[a]⟩::gs
  | g::gs,k+1,a => g::copyOrAt gs k a

private theorem copy_keeps_old (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ((Circuit.mk gs 0).wires w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).getD a false = _
    rw [ih _ (by rw [advance_len]; omega),getD_advance_lt g w a ha]

theorem copyOrAt_preserves (gs : List Gate) (k a : ℕ) (w : List Bool) (o : ℕ)
    (hk : k < gs.length) (ha : a < w.length+k)
    (eq : ((Circuit.mk gs 0).wires w).getD (w.length+k) false =
      ((Circuit.mk gs 0).wires w).getD a false) :
    (Circuit.mk (copyOrAt gs k a) o).eval w = (Circuit.mk gs o).eval w := by
  induction gs generalizing k w with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      have lt : a < w.length := by omega
      rw [Nat.add_zero,copy_keeps_old (g::gs) w a lt] at eq
      change ((Circuit.mk gs 0).wires (advance g w)).getD w.length false = _ at eq
      rw [copy_keeps_old _ _ _ (by rw [advance_len]; omega),getD_advance_eq] at eq
      have step : advance ⟨.and,[a]⟩ w = advance g w := by
        change w ++ [(_ && true)] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        rw [eq,Bool.and_true]
        rfl
      change (Circuit.mk gs o).eval (advance ⟨.and,[a]⟩ w) = (Circuit.mk gs o).eval (advance g w)
      rw [step]
    | succ k =>
      change (Circuit.mk (copyOrAt gs k a) o).eval (advance g w) =
        (Circuit.mk gs o).eval (advance g w)
      apply ih k _ (by simpa using hk) (by rw [advance_len]; omega)
      change ((Circuit.mk gs 0).wires (advance g w)).getD (w.length+(k+1)) false = ((Circuit.mk gs 0).wires (advance g w)).getD a false at eq
      simpa only [advance_len,show w.length+1+k = w.length+(k+1) by omega] using eq

private theorem copyOrAt_length (gs : List Gate) (k a : ℕ) : (copyOrAt gs k a).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => cases k <;> simp [copyOrAt,ih]

private theorem copyOrAt_mono (gs : List Gate) (k a o : ℕ) (hm : Monotone2 ⟨gs,o⟩) :
    Monotone2 ⟨copyOrAt gs k a,o⟩ := by
  induction gs generalizing k with
  | nil => exact hm
  | cons g gs ih =>
    cases k with
    | zero =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | tail
      · simp
      · exact hm b (List.mem_cons_of_mem _ tail)
    | succ k =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | tail
      · exact hm b (List.mem_cons_self ..)
      · exact ih k (fun x hx => hm x (List.mem_cons_of_mem _ hx)) b tail

private theorem copyOrAt_count (gs : List Gate) (a : ℕ) (k : Fin gs.length) (hk : k ∈ staticOrIds gs) :
    ((copyOrAt gs k.val a).filter isOrGate).length+1 = (gs.filter isOrGate).length := by
  induction gs with
  | nil => exact Fin.elim0 k
  | cons g gs ih =>
    refine Fin.cases ?_ (fun j => ?_) k hk
    · intro head
      have ho : isOrGate g = true := by
        by_contra bad
        simp [staticOrIds,bad] at head
      have off : isOrGate ⟨.and,[a]⟩ = false := rfl
      simp [copyOrAt,ho,off]
    · intro hj
      have tail : j ∈ staticOrIds gs := by
        by_cases ho : isOrGate g = true <;> simpa [staticOrIds,ho] using hj
      have h := ih j tail
      cases ho : isOrGate g <;> simp [copyOrAt,ho,h]

private theorem static_output_flag (gs : List Gate) (w : List Bool) (k : Fin gs.length)
    (hk : k ∈ staticOrIds gs) : k ∈ activeOrIds gs w ↔
      ((Circuit.mk gs 0).wires w).getD (w.length+k.val) false = true := by
  induction gs generalizing w with
  | nil => exact Fin.elim0 k
  | cons g gs ih =>
    refine Fin.cases ?_ (fun j => ?_) k hk
    · intro head
      have ho : isOrGate g = true := by
        by_contra bad
        simp [staticOrIds,bad] at head
      rw [activeOrIds_mem]
      change (isOrGate g && gateBool g w) = true ↔
        ((Circuit.mk gs 0).wires (advance g w)).getD w.length false = true
      rw [copy_keeps_old _ _ _ (by rw [advance_len];omega),getD_advance_eq,ho]
      rfl
    · intro hj
      have tail : j ∈ staticOrIds gs := by
        by_cases ho : isOrGate g = true <;> simpa [staticOrIds,ho] using hj
      rw [activeOrIds_mem]
      have h := (activeOrIds_mem gs (advance g w) j).symm.trans (ih (advance g w) j tail)
      change (trueOrFlags gs (advance g w)).getD j.val false = true ↔
        ((Circuit.mk gs 0).wires (advance g w)).getD (w.length+(j.val+1)) false = true
      simpa only [advance_len,show w.length+1+j.val = w.length+(j.val+1) by omega] using h

/-- Copying the earlier of two ORs with the same read set into a unary AND
at the later position saves one OR, keeps the gate count, and preserves
every output on the given input width. -/
theorem duplicate_or_to_and (C : Circuit) (hm : Monotone2 C) (n : ℕ)
    (a b : Fin C.gates.length) (ha : a ∈ staticOrIds C.gates) (hb : b ∈ staticOrIds C.gates)
    (ab : a < b) (eq : readAt C.gates n a.val = readAt C.gates n b.val) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
      (D.gates.filter isOrGate).length+1 = (C.gates.filter isOrGate).length ∧
      ∀ w : List Bool, w.length = n → D.eval w = C.eval w := by
  let D : Circuit := ⟨copyOrAt C.gates b.val (n+a.val),C.output⟩
  refine ⟨D,copyOrAt_mono C.gates b.val _ C.output hm,copyOrAt_length C.gates b.val (n+a.val),copyOrAt_count C.gates (n+a.val) b hb,?_⟩
  intro w len
  apply copyOrAt_preserves C.gates b.val (n+a.val) w C.output b.isLt (by rw [len]; exact Nat.add_lt_add_left ab n)
  rw [len]
  apply Bool.eq_iff_iff.mpr
  have same := (activeOrIds_iff_final_parent C.gates w b).trans
    (show (∃ x ∈ readAt C.gates w.length b.val, ((Circuit.mk C.gates 0).wires w).getD x false = true) ↔
      (∃ x ∈ readAt C.gates w.length a.val, ((Circuit.mk C.gates 0).wires w).getD x false = true)
      by rw [len,eq])
  have equiv := same.trans (activeOrIds_iff_final_parent C.gates w a).symm
  simpa only [len] using (static_output_flag C.gates w b hb).symm.trans (equiv.trans (static_output_flag C.gates w a ha))

theorem crown_or_reads_distinct_by_replacement (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (a b : Fin C.gates.length) (ha : a ∈ staticOrIds C.gates) (hb : b ∈ staticOrIds C.gates)
    (ab : a ≠ b) : readAt C.gates 24 a.val ≠ readAt C.gates 24 b.val := by
  intro eq
  have contradiction_of_lt (i j : Fin C.gates.length) (hi : i ∈ staticOrIds C.gates)
      (hj : j ∈ staticOrIds C.gates) (lt : i < j) (same : readAt C.gates 24 i.val = readAt C.gates 24 j.val) : False := by
    obtain ⟨D,dm,ds,dc,de⟩ := duplicate_or_to_and C hm 24 i j hi hj lt same
    have dr : Represents (fun u v : Fin 12 => decide (u ≠ v)) D :=
      fun u v => (de (oneEach u v) (by simp [oneEach])).trans (rep u v)
    have bound := crown_size_forty_requires_twenty_three_ors D dm dr (ds ▸ size)
    omega
  rcases lt_or_gt_of_ne ab with lt | gt
  · exact contradiction_of_lt a b ha hb lt eq
  · exact contradiction_of_lt b a hb ha gt eq.symm

end PEqualNP.Research.MissingCell
