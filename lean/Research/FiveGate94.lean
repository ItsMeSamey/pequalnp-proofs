import Research.FiveGateTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_17187.Transfer

-- Enumeration and circuit normalization follow the accepted proof of L_meta_17187.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate94 : srch 511 94 3 W0 seen0 L0 = false := by decide +kernel

private theorem base94 {m : ℕ} (F : (Fin m → Bool) → Bool) (a b : Fin 3 → Fin m) (hinja : Function.Injective a) (hinjb : Function.Injective b)
    (dis : ∀ u v, a u ≠ b v)
    (val : ∀ u v, F (ind (a u) (b v)) = (94 : ℕ).testBit (3*u.val+v.val)) (s : ℕ)
    (hs : HasCircuitSize m F s) : 6 ≤ s := by
  by_contra hlt
  obtain ⟨C, ok, hsz, hev⟩ := hs
  have hsz' : C.gates.length ≤ s := hsz
  let au : ℕ → Fin 3 := fun r => Fin.ofNat 3 (r / 3)
  let bv : ℕ → Fin 3 := fun r => Fin.ofNat 3 (r % 3)
  let w : ℕ → List Bool := fun r => List.ofFn (ind (a (au r)) (b (bv r)))
  have hA : ∀ u : Fin 3, ∃ t ∈ W0, ∀ r < 9, t.testBit r = decide (u = au r) := by decide +kernel
  have hB : ∀ u : Fin 3, ∃ t ∈ W0, ∀ r < 9, t.testBit r = decide (u = bv r) := by decide +kernel
  have hcov : Cov 9 W0 w := by
    intro i
    by_cases hi : i < m
    · have hg : ∀ r, (w r).getD i false = decide (⟨i, hi⟩ = a (au r) ∨ ⟨i, hi⟩ = b (bv r)) := by
        intro r
        rw [List.getD_eq_getElem _ _ (by simpa [w] using hi), List.getElem_ofFn]
        rfl
      by_cases h1 : ∃ u, a u = ⟨i, hi⟩
      · obtain ⟨u, hu⟩ := h1
        obtain ⟨t, ht, htv⟩ := hA u
        refine ⟨t, List.mem_cons_of_mem _ ht, fun r hr => ?_⟩
        rw [hg r, htv r hr, ← hu]
        apply decide_eq_decide.2
        constructor
        · rintro (e | e)
          · by_contra hne
            exact hne (hinja e)
          · exact (dis _ _ e).elim
        · intro e
          exact .inl (by rw [e])
      · by_cases h2 : ∃ u, b u = ⟨i, hi⟩
        · obtain ⟨u, hu⟩ := h2
          obtain ⟨t, ht, htv⟩ := hB u
          refine ⟨t, List.mem_cons_of_mem _ ht, fun r hr => ?_⟩
          rw [hg r, htv r hr, ← hu]
          apply decide_eq_decide.2
          constructor
          · rintro (e | e)
            · exact (dis _ _ e.symm).elim
            · by_contra hne
              exact hne (hinjb e)
          · intro e
            exact .inr (by rw [e])
        · refine ⟨0, List.mem_cons_self, fun r hr => ?_⟩
          rw [hg r, Nat.zero_testBit]
          apply decide_eq_false
          rintro (e | e)
          · exact h1 ⟨_, e.symm⟩
          · exact h2 ⟨_, e.symm⟩
    · refine ⟨0, List.mem_cons_self, fun r hr => ?_⟩
      rw [List.getD_eq_default _ _ (by simpa [w] using hi)]
      simp
  have hM : ∀ r < 9, (511 : ℕ).testBit r = true := by decide +kernel
  obtain ⟨D, hD, hDl, t, ht, htv⟩ := to_der 9 511 hM C.output C.gates W0 w m ok
    (fun r _ => by simp [w]) hcov
  have hgb : ∀ r < 9, (94 : ℕ).testBit (3*(au r).val+(bv r).val) = (94 : ℕ).testBit r := by decide +kernel
  have htg : ∀ r < 9, t.testBit r = (94 : ℕ).testBit r := by
    intro r hr
    rw [← htv r hr, ← hgb r hr, ← val (au r) (bv r)]
    exact hev _
  have bound : ∀ (D ws : List ℕ), (∀ x ∈ ws, x < 512) → Der 511 ws D → ∀ x ∈ D, x < 512 := by
    intro D
    induction D with
    | nil => intro ws _ _ x hx; simp at hx
    | cons d D ih =>
      intro ws hws hD x hx
      have hd : d < 512 := by
        rcases hD.1 with hd | rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
        · rcases List.mem_cons.1 hd with rfl | hd
          · norm_num
          · exact hws d hd
        · norm_num
        · exact Nat.xor_lt_two_pow (n := 9) (hws a ha) (by norm_num)
        · exact Nat.and_lt_two_pow (n := 9) a (hws b hb)
        · exact Nat.or_lt_two_pow (n := 9) (hws a ha) (hws b hb)
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hd
      · exact ih (d :: ws) (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hd
          · exact hws y hy) hD.2 x hx
  have hW : ∀ x ∈ 0 :: W0, x < 512 := by decide
  have ht512 : t < 2 ^ 9 := by
    rcases ht with ht | ht
    · exact hW t ht
    · exact bound D W0 (fun x hx => hW x (List.mem_cons_of_mem _ hx)) hD t ht
  have hteq : t = 94 := by
    apply Nat.eq_of_testBit_eq
    intro r
    by_cases hr : r < 9
    · exact htg r hr
    · have hp : 2 ^ 9 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ht512 hp),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) hp)]
  subst hteq
  have hg0 : (94 : ℕ) ∉ 0 :: W0 := by decide
  have := srch_sound 511 94 3 W0 seen0 L0 D hD (by omega) (ht.resolve_left hg0) hg0
    (fun d _ hd ho => (raw_L0 d (raw_mem ho)).resolve_left hd)
    (fun d _ hd hb => by
      rw [seen0_eq] at hb
      rcases List.mem_append.1 (maskOf_bit _ _ hb) with h | h
      · exact (hd h).elim
      · exact h)
  rw [certificate94] at this
  exact Bool.noConfusion this

private theorem induced_base94 (A : Fin 5 → Fin 5 → Bool) (r k : Fin 3 → Fin 5)
    (ir : Function.Injective r) (ik : Function.Injective k)
    (hcrown : ∀ u v, A (r u) (k v) = (94 : ℕ).testBit (3*u.val+v.val)) (C : Circuit)
    (hf : FanInTwo C) (hr : Represents A C) : 6 ≤ C.size := by
  let F : (Fin 10 → Bool) → Bool := fun x => C.eval (List.ofFn x)
  have input : ∀ u v : Fin 5, List.ofFn (ind (Fin.castAdd 5 u) (Fin.natAdd 5 v)) = oneEach u v := by
    decide
  apply base94 F (fun u => Fin.castAdd 5 (r u)) (fun v => Fin.natAdd 5 (k v))
  · intro u v he
    apply ir
    have e := congrArg (fun z : Fin 10 => z.val) he
    exact Fin.ext (by simpa only [Fin.val_castAdd] using e)
  · intro u v he
    apply ik
    apply Fin.ext
    have hh := congrArg Fin.val he
    simp only [Fin.val_natAdd] at hh
    omega
  · intro u v he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    have := (r u).isLt
    omega
  · intro u v
    change C.eval (List.ofFn (ind (Fin.castAdd 5 (r u)) (Fin.natAdd 5 (k v)))) = _
    rw [input,hr,hcrown]
  · exact ⟨C,hf,le_rfl,fun _ => rfl⟩

theorem PEqualNP.Outside.L_meta_19319 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (7576638 : ℕ).testBit (5*u.val+v.val))
    ![0, 2, 1] ![0, 1, 3] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19320 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576886 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (7576886 : ℕ).testBit (5*u.val+v.val))
    ![0, 2, 1] ![0, 1, 4] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19322 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577382 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (7577382 : ℕ).testBit (5*u.val+v.val))
    ![1, 2, 0] ![1, 0, 3] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19325 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7644470 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (7644470 : ℕ).testBit (5*u.val+v.val))
    ![0, 4, 1] ![0, 1, 4] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19326 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7712116 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (7712116 : ℕ).testBit (5*u.val+v.val))
    ![0, 4, 1] ![0, 2, 4] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19327 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16227576 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (16227576 : ℕ).testBit (5*u.val+v.val))
    ![0, 3, 1] ![0, 3, 4] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19328 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235644 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (16235644 : ℕ).testBit (5*u.val+v.val))
    ![0, 2, 1] ![0, 2, 4] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19332 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16238126 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (16238126 : ℕ).testBit (5*u.val+v.val))
    ![1, 3, 0] ![1, 0, 4] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19333 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (24151086 : ℕ).testBit (5*u.val+v.val))
    ![0, 4, 1] ![0, 1, 3] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19334 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24489316 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (24489316 : ℕ).testBit (5*u.val+v.val))
    ![1, 4, 0] ![2, 0, 3] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19335 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894510 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (24894510 : ℕ).testBit (5*u.val+v.val))
    ![0, 2, 1] ![0, 1, 3] (by decide) (by decide) (by decide) C hf hr
  omega

theorem PEqualNP.Outside.L_meta_19336 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨C,hf,hs,hr⟩
  have hh := induced_base94 (fun u v : Fin 5 => (24894758 : ℕ).testBit (5*u.val+v.val))
    ![1, 2, 0] ![1, 0, 3] (by decide) (by decide) (by decide) C hf hr
  omega
