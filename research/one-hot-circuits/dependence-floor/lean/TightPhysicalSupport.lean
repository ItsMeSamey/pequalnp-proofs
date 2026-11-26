import Research.MissingCellRigidity

namespace OnePerShore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

/-- A row is charged exactly if a positive cell in it has a zero below it
in the same column. -/
def nonminimumRows {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v w, A u v = true ∧ A w v = false

/-- Column version of the same physical dependence test. -/
def nonminimumCols {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u w, A u v = true ∧ A u w = false

def charged {n m : ℕ} (A : Fin n → Fin m → Bool) : ℕ :=
  (nonminimumRows A).card + (nonminimumCols A).card

theorem charged_le_live {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} (legal : Monotone2 C) (rep : Represents A C) :
    charged A ≤ (live C.gates (n+m) C.output).card := by
  apply mixed_support A _ (nonminimumRows A) (nonminimumCols A)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro u v w z h ht
    rw [←rep w z]
    apply eval_mono_live C (n+m) (oneEach u v) (oneEach w z) legal
      (by simp [oneEach]) (by simp [oneEach]) h
    simpa [rep u v] using ht

theorem physical_size_floor {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (bound : RepSizeAtMost A s) : charged A - 1 ≤ s := by
  obtain ⟨C, legal, size, rep⟩ := bound
  have h := charged_le_live legal rep
  have cap := live_card C.gates (n+m) C.output (fun g hg => (legal g hg).2)
  change C.gates.length ≤ s at size
  omega

/-- At the dependence floor, no repeated use, invalid gate input, dead gate
or unary gate can remain in the demanded physical circuit. -/
theorem tight_physical_sweep {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} (legal : Monotone2 C) (rep : Represents A C)
    (nonempty : 0 < charged A) (tight : C.size ≤ charged A - 1) :
    (live C.gates (n+m) C.output).card = charged A ∧
      C.size + 1 = charged A ∧ freshBinarySweep C.gates (n+m) C.output := by
  have h := charged_le_live legal rep
  have fan := fun g hg => (legal g hg).2
  have cap := live_card C.gates (n+m) C.output fan
  change C.gates.length ≤ charged A - 1 at tight
  change _ ∧ C.gates.length + 1 = _ ∧ _
  exact ⟨by omega, by omega, freshBinarySweep_of_max _ _ _ fan (by omega)⟩

end OnePerShore
