import DDMultiCost
import Q0FactorActual
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
private theorem fold_true {n : ℕ} (fs : List (Signal n)) (h : Signal n) (x : Fin n → Bool) :
    fs.foldl (join false) h x = true ↔ h x = true ∨ ∃ f ∈ fs, f x = true := by
  induction fs generalizing h with
  | nil => simp
  | cons f fs ih =>
    rw [List.foldl_cons, ih]
    simp only [join, Bool.false_eq_true, if_false, Bool.or_eq_true_iff, List.mem_cons]
    aesop

private theorem combined_true {n : ℕ} (g first : Signal n) (a u : List (Signal n))
    (x : Fin n → Bool) :
    combined g first a u x = true ↔
      (g x = true ∧ ∃ f ∈ first :: a, f x = true) ∨ ∃ f ∈ u, f x = true := by
  unfold combined
  rw [fold_true]
  change ((g x && a.foldl (join false) first x) = true ∨ _) ↔ _
  rw [Bool.and_eq_true, fold_true]
  simp only [List.mem_cons]
  aesop

private theorem join_roots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (roots : Finset ℕ) (dirty : ¬ BelowF G C g)
    (cover : ∀ x, graphFun G ∅ x = true ↔ ∃ t ∈ roots, gateVal n C t x = true)
    (flag : ℕ → Bool) (slot : ℕ → Option (Signal n)) (B : Bank n)
    (source : B (gateVal n C g))
    (live : ∃ t ∈ roots, flag t = true)
    (phys : ∀ t ∈ roots, physically B (slot t))
    (sem : ∀ t ∈ roots, ∀ x, gateVal n C t x =
      (if flag t then gateVal n C g x && denotation (slot t) x else denotation (slot t) x)) :
    ∃ first a u, B (gateVal n C g) ∧ B first ∧ (∀ s ∈ a, B s) ∧ (∀ s ∈ u, B s) ∧
      combined (gateVal n C g) first a u = graphFun G ∅ ∧
      a.length + u.length + 1 = roots.card := by
  classical
  unfold BelowF at dirty
  push_neg at dirty
  obtain ⟨z, hgz, hbad⟩ := dirty
  let sig (t : ℕ) : Signal n := denotation (slot t)
  have bank (t : ℕ) (ht : t ∈ roots) : B (sig t) := by
    have hh := phys t ht
    cases he : slot t with
    | some f =>
      have heq : sig t = f := by funext x; simp [sig, he, denotation]
      rw [heq]
      simpa [he, physically] using hh
    | none =>
      exfalso
      have yes : gateVal n C t z = true := by
        rw [sem t ht z, he]
        cases flag t <;> simp [denotation, hgz]
      have falseGraph := (cover z).mpr ⟨t,ht,yes⟩
      simp_all
  let A := (roots).filter fun t => flag t = true
  let U := (roots).filter fun t => ¬ flag t = true
  let as := A.toList.map sig
  let us := U.toList.map sig
  have amem (f : Signal n) : f ∈ as ↔ ∃ t ∈ roots, flag t = true ∧ sig t = f := by
    simp only [as, A, List.mem_map, Finset.mem_toList, Finset.mem_filter]
    aesop
  have umem (f : Signal n) : f ∈ us ↔ ∃ t ∈ roots, flag t ≠ true ∧ sig t = f := by
    simp only [us, U, List.mem_map, Finset.mem_toList, Finset.mem_filter]
    aesop
  obtain ⟨t, ht, hflag⟩ := live
  have hne := (amem (sig t)).2 ⟨t, ht, hflag, rfl⟩
  cases he : as with
  | nil => simp [he] at hne
  | cons first a =>
    have abank (f) (hh : f ∈ first :: a) : B f := by
      rw [← he] at hh
      obtain ⟨i, hi, _, rfl⟩ := (amem f).1 hh
      exact bank i hi
    refine ⟨first, a, us, source, abank first (by simp), fun f h => abank f (by simp [h]), ?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨i, hi, _, rfl⟩ := (umem f).1 hf
      exact bank i hi
    · funext x
      apply Bool.eq_iff_iff.mpr
      rw [combined_true, cover x, ← he]
      constructor
      · rintro (⟨hg, f, hm, hv⟩ | ⟨f, hm, hv⟩)
        · obtain ⟨i, hi, flagi, rfl⟩ := (amem f).1 hm
          exact ⟨i, hi, by simpa [sem i hi x, flagi, hg, sig] using hv⟩
        · obtain ⟨i, hi, flagi, rfl⟩ := (umem f).1 hm
          exact ⟨i, hi, by simpa [sem i hi x, flagi, sig] using hv⟩
      · rintro ⟨i, hi, hv⟩
        rw [sem i hi x] at hv
        by_cases h : flag i = true
        · have h2 : gateVal n C g x = true ∧ sig i x = true := by simpa [h, sig] using hv
          exact Or.inl ⟨h2.1, sig i, (amem _).2 ⟨i, hi, h, rfl⟩, h2.2⟩
        · exact Or.inr ⟨sig i, (umem _).2 ⟨i, hi, h, rfl⟩, by simpa [h, sig] using hv⟩
    · have hcount : A.card + U.card = (roots).card :=
        Finset.card_filter_add_card_filter_not (s := roots) (fun t => flag t = true)
      have hlen : as.length = A.card := by simp [as]
      have hul : us.length = U.card := by simp [us]
      rw [he, List.length_cons] at hlen
      omega

private theorem influence_forward {n g w : ℕ} {C : Circuit} (ao : IsAO2 n C)
    (h : Influence n C g w) : n+g ≤ w := by
  induction h with
  | source => exact le_rfl
  | step _ bound pin ih =>
    have := ao.2.1 _ bound _ pin
    omega

theorem strict_forward {n g w : ℕ} {C : Circuit} (ao : IsAO2 n C)
    (h : strictInfluence n C g w) : n+g < w := by
  obtain ⟨j,hj,rfl,u,hu,h⟩ := h
  exact (influence_forward ao h).trans_lt (ao.2.1 j hj u hu)

/-- Physical two-reader cap for the indexed prefix ending in both replacement ANDs,
before the final OR suffix. Roots are actual gate indices of that prefix. -/
theorem cap_alias_group {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (original C : Circuit)
    (least : IsLeastAO G original) (ao : IsAO2 n C) (roots : Finset ℕ)
    (valid : ∀ t ∈ roots, t < C.size) (cover : ∀ x, graphFun G ∅ x = true ↔
      ∃ t ∈ roots, gateVal n C t x = true) (near : C.size + roots.card ≤ original.size + 2)
    (g : ℕ) (hg : g < C.size) (dirty : ¬ BelowF G C g)
    (live : ∃ t ∈ roots, strictInfluence n C g (n+t))
    (dom : ∀ t ∈ roots, strictInfluence n C g (n+t) →
      ∀ x, gateVal n C t x = true → gateVal n C g x = true)
    (S : Finset ℕ) (gS : g ∈ S) (validS : ∀ i ∈ S, i<C.size)
    (aliases : ∀ i ∈ S, i ≠ g → strictInfluence n C g (n+i) ∧ gateVal n C i = gateVal n C g) :
    (S.biUnion (readers n C)).card ≤ 2 := by
  classical
  let p := multiCuts n C S
  let slot := fun t => physicalSlot n C p C.size (n+t)
  let flag := fun t => decide (strictInfluence n C g (n+t))
  obtain ⟨B,tr,bank⟩ := compiled_rows n C p C.size
  have sourceEq (x : Fin n → Bool) : gateVal n C g x = denotation (slot g) x := by
    apply multi_agree C ao S (by omega)
    intro i hi path
    by_cases ig : i=g
    · subst i; exact (Nat.lt_irrefl _ (strict_forward ao path)).elim
    have h1 := strict_forward ao (aliases i hi ig).1
    have h2 := strict_forward ao path
    omega
  have source : B (gateVal n C g) := by
    have ready := bank (n+g)
    change physically B (slot g) at ready
    cases he : slot g with
    | none =>
      have bad := sourceEq (fun _ => false)
      rw [he] at bad
      change W n C (fun _ => false) (n+g) = true at bad
      rw [zero_wire C ao _ (by omega)] at bad
      contradiction
    | some f =>
      have hf : gateVal n C g = f := funext fun x => by simpa [he,denotation] using sourceEq x
      rw [hf]
      simpa [he,physically] using ready
  have sem (t : ℕ) (ht : t ∈ roots) (x : Fin n → Bool) :
      gateVal n C t x = (if flag t then gateVal n C g x && denotation (slot t) x else denotation (slot t) x) := by
    have hb := valid t ht
    by_cases path : strictInfluence n C g (n+t)
    · simp only [flag,decide_eq_true path,if_true]
      cases h : gateVal n C g x with
      | false =>
        have off : gateVal n C t x ≠ true := by intro on; have := dom t ht path x on; simp_all
        simp_all
      | true =>
        simp only [Bool.true_and]
        apply multi_agree C ao S (by omega)
        intro i hi _
        by_cases eq : i=g
        · subst i; exact h
        · exact (congrFun (aliases i hi eq).2 x).trans h
    · simp only [flag,decide_eq_false path,if_false]
      apply multi_agree C ao S (by omega)
      intro i hi has
      by_cases eq : i=g
      · subst i; exact (path has).elim
      · exact (path (strict_trans (aliases i hi eq).1 has)).elim
  obtain ⟨a,as,us,sg,sa,sas,sus,eq,count⟩ := join_roots G C g roots dirty cover flag slot B source
    (by simpa [flag] using live) (fun t _ => bank _) sem
  obtain ⟨D,ad,eqD,size⟩ := circuit tr (gateVal n C g) a as us sg sa sas sus
  have min := least.2.2 D ad (eqD.trans eq)
  have budget : expense (seed n) (rows n C p C.size) + (S.biUnion (readers n C)).card ≤ C.size := by
    exact multi_cut_cost C ao S
  omega

theorem cap_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (original C : Circuit)
    (least : IsLeastAO G original) (ao : IsAO2 n C) (roots : Finset ℕ)
    (valid : ∀ t ∈ roots, t < C.size) (cover : ∀ x, graphFun G ∅ x = true ↔
      ∃ t ∈ roots, gateVal n C t x = true) (near : C.size + roots.card ≤ original.size + 2)
    (g : ℕ) (hg : g < C.size) (dirty : ¬ BelowF G C g)
    (live : ∃ t ∈ roots, strictInfluence n C g (n+t))
    (dom : ∀ t ∈ roots, strictInfluence n C g (n+t) →
      ∀ x, gateVal n C t x = true → gateVal n C g x = true) : (readers n C g).card ≤ 2 := by
  simpa using cap_alias_group G original C least ao roots valid cover near g hg dirty live dom
    {g} (by simp) (by simpa using hg) (by simp)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
