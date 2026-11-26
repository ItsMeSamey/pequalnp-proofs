import Research.CrownUniformTrace

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Research.MissingCell

private structure compared {k : ℕ} (z : Bool) (f : Fin k → Bool) : Prop where
  up : z = true → ∀ i, f i = true
  small : z = false → ∀ i j, f i = true → f j = true → i = j

private theorem zero_gate {k : ℕ} (hk : 3 ≤ k) (g : Gate) (z : List Bool) (w : Fin k → List Bool)
    (h : ∀ a, compared (z.getD a false) (fun i => (w i).getD a false))
    (hop : g.op = .and ∨ g.op = .or) (len : g.inputs.length ≤ 2)
    (uniform : ∀ i j, (isOrGate g && g.op.eval (g.inputs.map fun a => (w i).getD a false)) =
      (isOrGate g && g.op.eval (g.inputs.map fun a => (w j).getD a false))) :
    let base := g.op.eval (g.inputs.map fun a => z.getD a false)
    let act := fun i => g.op.eval (g.inputs.map fun a => (w i).getD a false)
    compared base act ∧ ∀ i, (isOrGate g && act i) = (isOrGate g && base) := by
  dsimp only
  rcases hop with hg | hg
  · rw [hg]
    constructor
    · constructor
      · simp only [GateOp.eval,List.all_map,List.all_eq_true]
        intro all i a ha
        exact (h a).up (all a ha) i
      · simp only [GateOp.eval,List.all_map,List.all_eq_false,List.all_eq_true]
        rintro ⟨a,ha,hf⟩ i j hi hj
        exact (h a).small (by simpa using hf) i j (hi a ha) (hj a ha)
    · simp [isOrGate,hg]
  · have hor : isOrGate g = true := by simp [isOrGate,hg]
    rw [hg] at uniform ⊢
    simp only [hor,Bool.true_and] at uniform ⊢
    let act := fun i => GateOp.or.eval (g.inputs.map fun a => (w i).getD a false)
    let base := GateOp.or.eval (g.inputs.map fun a => z.getD a false)
    have equal (i : Fin k) : act i = base := by
      cases hb : base with
      | true =>
        have somep : ∃ a ∈ g.inputs, z.getD a false = true := by simpa [base,GateOp.eval] using hb
        obtain ⟨a,ha,ht⟩ := somep
        have hat := (h a).up ht i
        simpa [act,GateOp.eval] using (show ∃ b ∈ g.inputs, (w i).getD b false = true from ⟨a,ha,hat⟩)
      | false =>
        by_contra! contra
        have hit : ∀ j : Fin k, ∃ a ∈ g.inputs, (w j).getD a false = true := by
          intro j
          have yesi : act i = true := by simpa only [Bool.not_eq_false] using contra
          have yes : act j = true := (uniform j i).trans yesi
          simpa [act,GateOp.eval] using yes
        choose a ha hat using hit
        let e (j : Fin k) : g.inputs.toFinset := ⟨a j, List.mem_toFinset.mpr (ha j)⟩
        have inj : Function.Injective e := by
          intro u v he
          have same : a u = a v := congrArg Subtype.val he
          have off : z.getD (a u) false = false := by
            have all : ∀ b ∈ g.inputs, z.getD b false = false := by
              simpa [base,GateOp.eval] using hb
            exact all (a u) (ha u)
          exact (h _).small off u v (hat u) (same ▸ hat v)
        have card := Fintype.card_le_of_injective e inj
        simp only [Fintype.card_fin,Fintype.card_coe] at card
        have := List.toFinset_card_le g.inputs
        omega
    exact ⟨⟨fun hb i => (equal i).trans hb, fun hf i j hi _ => False.elim (by
      change act i = true at hi
      change base = false at hf
      rw [equal i,hf] at hi
      contradiction)⟩,equal⟩

private theorem uniform_zero_flags {k : ℕ} (hk : 3 ≤ k) (gs : List Gate) (z : List Bool)
    (w : Fin k → List Bool) (len : ∀ i, (w i).length = z.length)
    (inv : ∀ a, compared (z.getD a false) (fun i => (w i).getD a false))
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (same : ∀ i j, trueOrFlags gs (w i) = trueOrFlags gs (w j)) :
    ∀ i, trueOrFlags gs (w i) = trueOrFlags gs z := by
  induction gs generalizing w z with
  | nil => simp [trueOrFlags]
  | cons g gs ih =>
    have unif i j := congrArg List.head? (same i j)
    simp only [trueOrFlags,List.head?_cons,Option.some.injEq] at unif
    obtain ⟨cmp,flags⟩ := zero_gate hk g z w inv (mono g (List.mem_cons_self ..)).1
      (mono g (List.mem_cons_self ..)).2 unif
    have nextInv (a : ℕ) : compared ((advance g z).getD a false) (fun i => (advance g (w i)).getD a false) := by
      by_cases ha : a < z.length
      · have ew (i : Fin k) : (advance g (w i)).getD a false = (w i).getD a false :=
            getD_advance_lt _ _ _ (by rw [len]; exact ha)
        simpa only [getD_advance_lt g z a ha,ew] using inv a
      · by_cases eq : a = z.length
        · subst a
          have ew (i : Fin k) : (advance g (w i)).getD z.length false =
              g.op.eval (g.inputs.map fun a => (w i).getD a false) := by rw [←len i,getD_advance_eq]
          simpa only [getD_advance_eq,ew] using cmp
        · have ez : (advance g z).getD a false = false := getD_missing (by rw [advance_len];omega)
          have ew (i : Fin k) : (advance g (w i)).getD a false = false :=
            getD_missing (by rw [advance_len,len];omega)
          simp only [ez,ew]
          exact ⟨by simp,by simp⟩
    have tail := ih (advance g z) (fun i => advance g (w i))
      (fun i => by simp [advance_len,len]) nextInv (fun b hb => mono b (List.mem_cons_of_mem _ hb))
      (fun i j => congrArg List.tail (same i j))
    intro i
    exact congrArg₂ List.cons (flags i) (tail i)

private theorem raw_getD_unique {k n : ℕ} (e : Fin k ↪ Fin n) (a : ℕ) (i j : Fin k)
    (hi : (oneEach (e i) (e i)).getD a false = true)
    (hj : (oneEach (e j) (e j)).getD a false = true) : i = j := by
  by_cases hlt : a < n
  · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,hlt] at hi hj
    exact e.injective (hi.symm.trans hj)
  · by_cases hb : a-n < n
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt hlt,hb] at hi hj
      exact e.injective (hi.symm.trans hj)
    · simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.le_of_not_gt hlt,hb] at hi

theorem crown_signature_equals_zero {k n : ℕ} (hk : 3 ≤ k) (e : Fin k ↪ Fin n) (C : Circuit)
    (hm : Monotone2 C) (uniform : ∀ i j, trueOrFlags C.gates (oneEach (e i) (e i)) =
      trueOrFlags C.gates (oneEach (e j) (e j))) :
    ∀ i, trueOrFlags C.gates (oneEach (e i) (e i)) =
      trueOrFlags C.gates (List.replicate (n+n) false) := by
  apply uniform_zero_flags hk _ _ _ (fun i => by simp [oneEach]) _ hm uniform
  intro a
  have ez : (List.replicate (n+n) false).getD a false = false := by
    by_cases hb : a<n+n <;> simp [List.getD_eq_getElem?_getD,hb]
  rw [ez]
  exact ⟨by simp, fun _ i j hi hj => raw_getD_unique e a i j hi hj⟩

theorem nonbaseline_signature_at_most_two {n : ℕ} (C : Circuit) (hm : Monotone2 C) (b : List Bool)
    (diff : b ≠ trueOrFlags C.gates (List.replicate (n+n) false)) :
    (Finset.univ.filter (fun i : Fin n => trueOrFlags C.gates (oneEach i i) = b)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => trueOrFlags C.gates (oneEach i i) = b)
  let e : Fin S.card ↪ Fin n := (S.orderIsoOfFin rfl).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  have he (i : Fin S.card) : trueOrFlags C.gates (oneEach (e i) (e i)) = b :=
    (Finset.mem_filter.mp ((S.orderIsoOfFin rfl i).property)).2
  change S.card ≤ 2
  by_contra! gt
  let i : Fin S.card := ⟨0,by omega⟩
  exact diff ((he i).symm.trans (crown_signature_equals_zero (by omega : 3 ≤ S.card) e C hm
    (fun i j => (he i).trans (he j).symm) i))

end CrownDiagonalCharge
