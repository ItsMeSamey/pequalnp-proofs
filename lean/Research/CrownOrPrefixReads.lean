import Research.CrownIndexedOrValues
import Research.CrownSingleOrChain

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem nest_input_preserved (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    ((Circuit.mk gs 0).wires w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).getD i false = _
    rw [ih _ (by rw [advance_len]; omega), getD_advance_lt g w i hi]

theorem nest_read_lt (gs : List Gate) (n k i : Nat) (read : i ∈ readAt gs n k) : i < n+k := by
  induction gs generalizing n k with
  | nil => simp [readAt] at read
  | cons gate tail ih =>
    cases k with
    | zero =>
      change i ∈ orReads gate n at read
      unfold orReads at read
      split at read
      · simpa using (Finset.mem_filter.mp read).2
      · simp at read
    | succ k =>
      have := ih (n+1) k read
      omega

theorem nest_prefix_wire (gs : List Gate) (w : List Bool) (n i : Nat) (hi : i < w.length+n) :
    ((Circuit.mk (gs.take n) 0).wires w).getD i false =
    ((Circuit.mk gs 0).wires w).getD i false := by
  induction gs generalizing w n with
  | nil => simp
  | cons g gs ih =>
    cases n with
    | zero =>
      change w.getD i false = _
      exact (nest_input_preserved _ _ _ (by omega)).symm
    | succ n =>
      change ((Circuit.mk (gs.take n) 0).wires (advance g w)).getD i false =
          ((Circuit.mk gs 0).wires (advance g w)).getD i false
      exact ih _ _ (by rw [advance_len]; omega)

theorem nest_prefix_flag (gs : List Gate) (w : List Bool) (n k : Nat) (hk : k < n) :
    (trueOrFlags (gs.take n) w).getD k false = (trueOrFlags gs w).getD k false := by
  induction gs generalizing w n k with
  | nil => simp
  | cons g gs ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases k with
      | zero => rfl
      | succ k => exact ih (advance g w) n k (by omega)

theorem nest_flag_as_wire (gs : List Gate) (x y : List Bool) (k : Nat)
    (hot : (trueOrFlags gs x).getD k false = true) :
    (trueOrFlags gs y).getD k false = ((Circuit.mk gs 0).wires y).getD (y.length+k) false := by
  induction gs generalizing x y k with
  | nil => simp [trueOrFlags,List.getD_eq_getElem?_getD] at hot
  | cons g gs ih =>
    cases k with
    | zero =>
      change (isOrGate g && _) = true at hot
      have hor := (Bool.and_eq_true_iff.mp hot).1
      change (isOrGate g && _) = ((Circuit.mk gs 0).wires (advance g y)).getD (y.length+0) false
      simp only [hor,Bool.true_and,Nat.add_zero]
      rw [nest_input_preserved _ _ _ (by rw [advance_len]; omega),getD_advance_eq]
    | succ k =>
      have e := ih (advance g x) (advance g y) k hot
      rw [advance_len] at e
      change (trueOrFlags gs (advance g y)).getD k false = ((Circuit.mk gs 0).wires (advance g y)).getD (y.length+(k+1)) false
      rw [show y.length+(k+1) = y.length+1+k by omega]
      exact e

/-- A singleton-hot wire before the second active OR equals the raw singleton
literal, the first OR output, or constant true on every length-n input. -/
theorem nest_predecessor_semantics (gs : List Gate) (n : Nat) (p : {w : List Bool // w.length = n})
    (a g h i : Nat) (singleton : ∀ j, p.val.getD j false = true ↔ j = a)
    (mono : ∀ op ∈ gs, op.op = .and ∨ op.op = .or)
    (fired : (trueOrFlags gs p.val).getD g false = true)
    (unique : ∀ j < h, (trueOrFlags gs p.val).getD j false = true → j = g)
    (literal : ∀ q : {w : List Bool // w.length = n}, q.val.getD a false = true →
      ((Circuit.mk gs 0).wires q.val).getD (n+g) false = true)
    (bound : i < n+h) (hot : ((Circuit.mk gs 0).wires p.val).getD i false = true) :
    let X := {w : List Bool // w.length = n}
    let W := fun (j : Nat) => {q : X | ((Circuit.mk gs 0).wires q.val).getD j false = true}
    W i = {q : X | q.val.getD a false = true} ∨ W i = W (n+g) ∨ W i = Set.univ := by
  let X := {w : List Bool // w.length = n}
  let r : Set X := {q | q.val.getD a false = true}
  let G : Set X := {q | ((Circuit.mk gs 0).wires q.val).getD (n+g) false = true}
  have eq (q : X) := nest_prefix_wire gs q.val h i (by rw [q.property]; exact bound)
  have chain := prefix_one_or_chain (gs.take h) (fun q : X => q.val) p r G (fun _ => literal _)
    (fun q => q.property.trans p.property.symm)
    (fun j hj => Or.inl (by obtain rfl := (singleton j).mp hj; rfl))
    (fun gate hg => mono gate (List.mem_of_mem_take hg)) (by
      intro j on
      have jh : j < h := by
        by_contra! large
        have len := trueOrFlags_length (gs.take h) p.val
        rw [List.length_take] at len
        rw [getD_missing (by omega : (trueOrFlags (gs.take h) p.val).length ≤ j)] at on
        contradiction
      have same := unique j jh ((nest_prefix_flag gs p.val h j jh).symm.trans on)
      subst j
      ext q
      simp only [Set.mem_ofPred_eq,G]
      rw [nest_prefix_flag gs q.val h g jh,nest_flag_as_wire gs _ _ g fired,q.property])
    i ((eq p).trans hot)
  simpa only [eq,r,G] using chain

end PEqualNP.Research.MissingCell
