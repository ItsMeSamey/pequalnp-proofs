import ExactPlaneGaussian
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card

namespace ExactPlaneGaussian
variable {d : ℕ} {I : Type*}

theorem pivot_keys_nodup {s : Bank d I} (hs : Echelon s) :
    (s.map Prod.fst).Nodup := by
  induction hs with
  | nil => simp
  | @snoc s i p _ one zeros ih =>
    rw [List.map_append]
    change ((s.map Prod.fst) ++ [i]).Nodup
    rw [List.nodup_append_comm]
    simp only [List.singleton_append,List.nodup_cons]
    refine ⟨?_,ih⟩
    intro mem
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp mem
    have z := zeros a ha
    rw [eq,one] at z
    exact one_ne_zero z

theorem bank_length_le {s : Bank d I} (hs : Echelon s) : s.length ≤ d := by
  simpa using (pivot_keys_nodup hs).length_le_card

theorem build_length_le [DecidableEq I] (v : I → V d) (A : List I) :
    (build v A).length ≤ d := bank_length_le (build_echelon v A)

#print axioms build_length_le
end ExactPlaneGaussian
