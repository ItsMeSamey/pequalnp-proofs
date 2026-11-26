import T2SoleOrSplice
namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RawIsolation

theorem vec_get {n : Nat} (s : Finset (Fin n)) (i : Nat) :
    (vector s).getD i false = if hi : i<n then decide ((⟨i,hi⟩ : Fin n)∈s) else false := by
  by_cases hi : i<n <;> simp [vector,List.getD_eq_getElem?_getD,hi]

theorem off_insert {n : Nat} (s : Finset (Fin n)) (x : Fin n) :
    AgreeOff x.val (vector s) (vector (insert x s)) := by
  constructor
  · simp [vector]
  · intro i diff
    rw [vec_get,vec_get]
    by_cases hi : i<n
    · have ne : (⟨i,hi⟩ : Fin n)≠x := fun eq => diff (congrArg Fin.val eq)
      simp [hi,ne]
    · simp [hi]

end T2SoleOrSplice
