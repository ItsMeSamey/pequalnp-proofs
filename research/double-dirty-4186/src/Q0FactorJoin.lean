import Q0Factor
import Q0Aggregation

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

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

theorem join_from_top_slots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : TopForm G C) (dirty : ¬ BelowF G C g)
    (flag : ℕ → Bool) (slot : ℕ → Option (Signal n)) (B : Bank n)
    (source : B (gateVal n C g))
    (live : ∃ t ∈ tops G C, flag t = true)
    (phys : ∀ t ∈ tops G C, physically B (slot t))
    (sem : ∀ t ∈ tops G C, ∀ x, gateVal n C t x =
      (if flag t then gateVal n C g x && denotation (slot t) x else denotation (slot t) x)) :
    ∃ first a u, B (gateVal n C g) ∧ B first ∧ (∀ s ∈ a, B s) ∧ (∀ s ∈ u, B s) ∧
      combined (gateVal n C g) first a u = graphFun G ∅ ∧
      a.length + u.length = (orT G C).card := by
  classical
  unfold BelowF at dirty
  push_neg at dirty
  obtain ⟨z, hgz, hbad⟩ := dirty
  let sig (t : ℕ) : Signal n := denotation (slot t)
  have bank (t : ℕ) (ht : t ∈ tops G C) : B (sig t) := by
    have hh := phys t ht
    cases he : slot t with
    | some f =>
      have heq : sig t = f := by funext x; simp [sig, he, denotation]
      rw [heq]
      simpa [he, physically] using hh
    | none =>
      exfalso
      have ht' := ht
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht'
      have yes : gateVal n C t z = true := by
        rw [sem t ht z, he]
        cases flag t <;> simp [denotation, hgz]
      have falseGraph := ht'.2.2 z yes
      simp_all
  let A := (tops G C).filter fun t => flag t = true
  let U := (tops G C).filter fun t => ¬ flag t = true
  let as := A.toList.map sig
  let us := U.toList.map sig
  have amem (f : Signal n) : f ∈ as ↔ ∃ t ∈ tops G C, flag t = true ∧ sig t = f := by
    simp only [as, A, List.mem_map, Finset.mem_toList, Finset.mem_filter]
    aesop
  have umem (f : Signal n) : f ∈ us ↔ ∃ t ∈ tops G C, flag t ≠ true ∧ sig t = f := by
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
      rw [combined_true, graph_iff_top G C edge least x, ← he]
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
    · have hcount : A.card + U.card = (tops G C).card :=
        Finset.card_filter_add_card_filter_not (s := tops G C) (fun t => flag t = true)
      have hlen : as.length = A.card := by simp [as]
      have hul : us.length = U.card := by simp [us]
      rw [he, List.length_cons] at hlen
      have count := clean_or_count G C edge least form
      omega

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
