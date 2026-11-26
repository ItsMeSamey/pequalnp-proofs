import Research.CrownIdentifyEval
import Research.ThresholdFactors

namespace PEqualNP.Research.CrownIdentify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

def bits (s : Finset (Fin 12)) : List Bool := List.ofFn fun i : Fin 12 => decide (i ∈ s)

private theorem bits_mono (s t : Finset (Fin 12)) (sub : s ⊆ t) (k : ℕ) :
    (bits s).getD k false = true → (bits t).getD k false = true := by
  by_cases lt : k < 12
  · simp only [bits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,lt,↓reduceDIte,Option.getD_some,decide_eq_true_eq]
    exact fun h => sub h
  · rw [getD_missing (show (bits s).length ≤ k by simp [bits]; omega)]
    simp

private theorem bits_append_mono (a b c d : Finset (Fin 12)) (ab : a ⊆ b) (cd : c ⊆ d) (k : ℕ) :
    (bits a ++ bits c).getD k false = true → (bits b ++ bits d).getD k false = true := by
  have la : (bits a).length = 12 := by simp [bits]
  have lb : (bits b).length = 12 := by simp [bits]
  by_cases lt : k < 12
  · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left (show k < (bits a).length by omega),
      List.getElem?_append_left (show k < (bits b).length by omega)] using bits_mono a b ab k
  · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_right (show (bits a).length ≤ k by omega),
      List.getElem?_append_right (show (bits b).length ≤ k by omega),la,lb] using bits_mono c d cd (k-12)

theorem foldCrown_threshold (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (s : Finset (Fin 12)) :
    (foldCrown C).eval (bits s) = true ↔ 2 ≤ s.card := by
  rw [foldCrown_eval _ _ (by simp [bits])]
  let f (a b : Finset (Fin 12)) := C.eval (bits a ++ bits b) = true
  apply ThresholdFactors.identify f ?_ ?_ s
  · intro a b c d ab cd
    apply eval_mono_live C 24 (bits a ++ bits c) (bits b ++ bits d) hm
        (by simp [bits]) (by simp [bits])
    intro k _
    exact bits_append_mono a b c d ab cd k
  · intro u v
    have eq : bits {u} ++ bits {v} = oneEach u v := by simp [bits,oneEach]
    change C.eval (bits {u} ++ bits {v}) = true ↔ _
    rw [eq,rep u v]
    simp

theorem bits_from_assignment (v : Fin 12 → Bool) :
    bits (Finset.univ.filter (fun i => v i)) = List.ofFn v := by
  unfold bits
  congr 1
  funext i
  simp

theorem foldCrown_threshold_assignment (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (v : Fin 12 → Bool) :
    (foldCrown C).eval (List.ofFn v) = true ↔ 2 ≤ (Finset.univ.filter (fun i => v i)).card := by
  simpa only [bits_from_assignment] using foldCrown_threshold C hm rep (Finset.univ.filter (fun i => v i))

theorem compressed_threshold_exists (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + pairCount C.gates 24 = C.size ∧
      (D.gates.filter isOrGate).length + pairCount C.gates 24 = (C.gates.filter isOrGate).length ∧
      ∀ s : Finset (Fin 12), D.eval (bits s) = true ↔ 2 ≤ s.card :=
  ⟨foldCrown C,compress_mono _ _ _ _ _ hm,(foldCrown_counts C).1,(foldCrown_counts C).2,
    foldCrown_threshold C hm rep⟩

end PEqualNP.Research.CrownIdentify
