import LiveSlice
import MaskCode24202
import Numeric24202

namespace Probe24202
open ProbeFrontier
private abbrev M := Mask (Fin 21)

private theorem mem_code_iff {S : Finset M} {a : M} : encode a ∈ codes S ↔ a ∈ S := by
  rw [mem_codes]
  constructor
  · rintro ⟨x, hx, eq⟩
    exact encode_injective eq ▸ hx
  · intro h; exact ⟨a,h,rfl⟩

private theorem retain_or_erase (U : Finset M) (a : M) :
    codes U ∈ [(codes (insert a U)).erase (encode a), codes (insert a U)] := by
  by_cases h : a ∈ U
  · simp [Finset.insert_eq_of_mem h]
  · have eq : (insert a U).erase a = U := Finset.erase_insert h
    rw [← codes_erase, eq]
    simp

private theorem fresh_code {S : Finset M} {y : M} (h : ¬available S y) :
    encode y ≠ 0 ∧ encode y ≠ Numeric24202.ones ∧ encode y ∉ codes S := by
  have hz : y ≠ zero := fun e => h (.inr (.inl e))
  have ho : y ≠ one := fun e => h (.inr (.inr e))
  have hs : y ∉ S := fun e => h (.inl e)
  refine ⟨fun e => hz (encode_injective ?_), fun e => ho (encode_injective ?_), ?_⟩
  · simpa [encode_zero] using e
  · simpa [encode_one, Numeric24202.ones] using e
  · simpa [mem_code_iff] using hs

private theorem unary_child {U : Finset M} {a y : M} (h : ¬available (insert a U) y) :
    codes (insert y U) ∈ Numeric24202.produced (codes (insert a U)) (encode a) none (encode y) := by
  obtain ⟨h0,h1,hs⟩ := fresh_code h
  have hy : y ∉ U := fun hu => h (.inl (Finset.mem_insert_of_mem hu))
  have guard : ¬ ((encode y == 0 || encode y == Numeric24202.ones || (codes (insert a U)).contains (encode y)) = true) := by
    simp [h0, h1, hs]
  rw [Numeric24202.produced, ite_eq_right guard]
  simp only [List.mem_map]
  exact ⟨codes U, retain_or_erase U a, (codes_insert hy).symm⟩

private theorem binary_child {U : Finset M} {a z y : M}
    (h : ¬available (insert a (insert z U)) y) :
    codes (insert y U) ∈ Numeric24202.produced (codes (insert a (insert z U)))
      (encode a) (some (encode z)) (encode y) := by
  obtain ⟨h0,h1,hs⟩ := fresh_code h
  have hy : y ∉ U := fun hu => h (.inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)))
  have guard : ¬ ((encode y == 0 || encode y == Numeric24202.ones || (codes (insert a (insert z U))).contains (encode y)) = true) := by
    simp [h0, h1, hs]
  rw [Numeric24202.produced, ite_eq_right guard]
  simp only [List.mem_map]
  refine ⟨codes U, List.mem_flatMap.mpr ⟨codes (insert z U), retain_or_erase _ _, ?_⟩,
    (codes_insert hy).symm⟩
  exact retain_or_erase U z

private theorem step_neg {U : Finset M} {a y : M} (b t : ℕ)
    (h : ¬available (insert a U) y) (hv : encode y = Numeric24202.ones ^^^ encode a) :
    (b,t,codes (insert y U)) ∈ Numeric24202.next b (t+1) (codes (insert a U)) := by
  unfold Numeric24202.next
  apply List.mem_append.mpr
  left
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false,
    Nat.add_sub_cancel, List.mem_flatMap, List.mem_map]
  refine ⟨encode a, ?_, codes (insert y U), ?_, rfl⟩
  · exact mem_code_iff.mpr (Finset.mem_insert_self ..)
  · rw [← hv]; exact unary_child h

private theorem step_binary {U : Finset M} {a z y : M} (b t : ℕ)
    (h : ¬available (insert a (insert z U)) y) (hlt : encode z < encode a)
    (hv : encode y ∈ [encode a &&& encode z, encode a ||| encode z]) :
    (b,t,codes (insert y U)) ∈ Numeric24202.next (b+1) t (codes (insert a (insert z U))) := by
  unfold Numeric24202.next
  apply List.mem_append.mpr
  right
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false,
    Nat.add_sub_cancel, List.mem_flatMap]
  refine ⟨encode a, mem_code_iff.mpr (Finset.mem_insert_self ..), encode z,
    mem_code_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)), ?_⟩
  simp only [hlt, ite_true, List.mem_flatMap, List.mem_map]
  exact ⟨encode y,hv,codes (insert y U),binary_child h,rfl⟩

/-- A live transition at any remaining tail budget is a numeric child. -/
theorem exactOp_next {T P : Finset M} {neg : Bool} {y : M} (b t : ℕ)
    (op : ExactOp P neg y) (hy : y ∈ T) (fresh : ¬available (T.erase y ∪ P) y) :
    (b,t,codes T) ∈ Numeric24202.next
      (b + if neg then 0 else 1) (t + if neg then 1 else 0) (codes (T.erase y ∪ P)) := by
  have restore : insert y (T.erase y) = T := Finset.insert_erase hy
  suffices r : (b,t,codes (insert y (T.erase y))) ∈ Numeric24202.next
      (b + if neg then 0 else 1) (t + if neg then 1 else 0) (codes (T.erase y ∪ P)) by
    rwa [restore] at r
  cases op with
  | neg a =>
    simpa only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Finset.union_insert, Finset.union_singleton] using
      step_neg (U := T.erase _) b t (a := a) (y := fun p => !(a p))
        (by simpa [Finset.union_insert, Finset.union_singleton] using fresh) (encode_not a)
  | conj a z haz =>
    rcases lt_or_gt_of_ne (fun e => haz (encode_injective e)) with h|h
    · simpa only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Finset.union_insert, Finset.union_singleton, Finset.insert_comm] using
        step_binary (U := T.erase _) b t (a := z) (z := a) (y := fun p => a p && z p)
          (by simpa [Finset.union_insert, Finset.union_singleton,Finset.insert_comm] using fresh) h
          (by simp [encode_and, Nat.and_comm])
    · simpa only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Finset.union_insert, Finset.union_singleton, Finset.insert_comm] using
        step_binary (U := T.erase _) b t (a := a) (z := z) (y := fun p => a p && z p)
          (by simpa [Finset.union_insert, Finset.union_singleton,Finset.insert_comm] using fresh) h
          (by simp [encode_and])
  | disj a z haz =>
    rcases lt_or_gt_of_ne (fun e => haz (encode_injective e)) with h|h
    · simpa only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Finset.union_insert, Finset.union_singleton, Finset.insert_comm] using
        step_binary (U := T.erase _) b t (a := z) (z := a) (y := fun p => a p || z p)
          (by simpa [Finset.union_insert, Finset.union_singleton,Finset.insert_comm] using fresh) h
          (by simp [encode_or, Nat.or_comm])
    · simpa only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Finset.union_insert, Finset.union_singleton, Finset.insert_comm] using
        step_binary (U := T.erase _) b t (a := a) (z := z) (y := fun p => a p || z p)
          (by simpa [Finset.union_insert, Finset.union_singleton,Finset.insert_comm] using fresh) h
          (by simp [encode_or])
end Probe24202
