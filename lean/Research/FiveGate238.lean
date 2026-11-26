import Research.FiveGateTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_17187.Transfer

private theorem induced_three_crown (A : Fin 5 → Fin 5 → Bool) (r k : Fin 3 → Fin 5)
    (hcrown : ∀ u v, A (r u) (k v) = decide (u ≠ v)) (C : Circuit)
    (hf : FanInTwo C) (hr : Represents A C) : 6 ≤ C.size := by
  let F : (Fin 10 → Bool) → Bool := fun x => C.eval (List.ofFn x)
  have input : ∀ u v : Fin 5, List.ofFn (ind (Fin.castAdd 5 u) (Fin.natAdd 5 v)) = oneEach u v := by
    decide
  apply base F (fun u => Fin.castAdd 5 (r u)) (fun v => Fin.natAdd 5 (k v))
  · constructor
    · intro u v
      change C.eval (List.ofFn (ind (Fin.castAdd 5 (r u)) (Fin.natAdd 5 (k v)))) = _
      rw [input,hr,hcrown]
    · intro u v he
      have hh := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
      have := (r u).isLt
      omega
  · exact ⟨C,hf,le_rfl,fun _ => rfl⟩

theorem PEqualNP.Outside.L_meta_19317 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247678 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (3247678 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 4] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19318 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247934 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (3247934 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 3] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19321 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577150 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (7577150 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 4] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19323 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577398 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (7577398 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 4] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19324 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577402 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (7577402 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 3] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19329 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236082 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (16236082 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 4] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19330 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236086 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (16236086 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 1, 4] (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19331 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236156 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_three_crown (fun u v : Fin 5 => (16236156 : ℕ).testBit (5*u.val+v.val))
    ![0, 1, 2] ![0, 2, 4] (by decide) C hf hr
  omega
