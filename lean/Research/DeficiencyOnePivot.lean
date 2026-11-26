import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace DeficiencyOnePivot

variable {C V : Type*} [Fintype C] [Fintype V]

/-- A matching covers every clause except u. The stored value f u is ignored. -/
def Almost (edge : C → V → Prop) (u : C) (f : C → V) : Prop :=
  (∀ c, c ≠ u → edge c (f c)) ∧
  ∀ c d, c ≠ u → d ≠ u → f c = f d → c = d

/-- If one clause is exposed in a maximum incidence matching, a satisfiable
formula admits a single literal restriction leaving a matched formula. -/
theorem pivot (edge : C → V → Prop) (sign : C → V → Bool) (a : V → Bool)
    (sat : ∀ c, ∃ v, edge c v ∧ a v = sign c v)
    (one : ∃ u f, Almost edge u f)
    (noFull : ¬ ∃ f : C → V, Function.Injective f ∧ ∀ c, edge c (f c)) :
    ∃ v : V, ∃ u : C, edge u v ∧ a v = sign u v ∧
      ∃ f : C → V, ∀ c, ¬ (edge c v ∧ a v = sign c v) →
        edge c (f c) ∧ f c ≠ v ∧
        ∀ d, ¬ (edge d v ∧ a v = sign d v) → f c = f d → c = d := by
  classical
  let good (p : C × (C → V)) := Finset.univ.filter
    (fun c => c ≠ p.1 ∧ a (p.2 c) = sign c (p.2 c))
  let candidates := Finset.univ.filter (fun p : C × (C → V) => Almost edge p.1 p.2)
  have ne : candidates.Nonempty := by
    obtain ⟨u, f, hu⟩ := one
    exact ⟨(u, f), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
  obtain ⟨⟨u, f⟩, hp, best⟩ := candidates.exists_max_image (fun p => (good p).card) ne
  obtain ⟨incident, inj⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨v, huv, htrue⟩ := sat u
  let g (c : C) := if c = u then v else f c
  have owner : ∃ d, d ≠ u ∧ f d = v := by
    by_contra! free
    apply noFull
    refine ⟨g, ?_, ?_⟩
    · intro c d h
      by_cases hc : c = u <;> by_cases hd : d = u
      · exact hc.trans hd.symm
      · exact False.elim (free d hd (by simpa [g, hc, hd] using h.symm))
      · exact False.elim (free c hc (by simpa [g, hc, hd] using h))
      · exact inj c d hc hd (by simpa [g, hc, hd] using h)
    · intro c
      by_cases h : c = u
      · simpa [g, h] using huv
      · simpa [g, h] using incident c h
  obtain ⟨d, hdu, hdv⟩ := owner
  have hdtrue : a v = sign d v := by
    by_contra bad
    have alt : Almost edge d g := by
      constructor
      · intro c _
        by_cases h : c = u
        · simpa [g, h] using huv
        · simpa [g, h] using incident c h
      · intro i j hi hj heq
        by_cases iu : i = u <;> by_cases ju : j = u
        · exact iu.trans ju.symm
        · exact False.elim (hj (inj j d ju hdu (by simpa [g, iu, ju, hdv] using heq.symm)))
        · exact False.elim (hi (inj i d iu hdu (by simpa [g, iu, ju, hdv] using heq)))
        · exact inj i j iu ju (by simpa [g, iu, ju] using heq)
    have le := best (d, g) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, alt⟩)
    have strict : good (u, f) ⊂ good (d, g) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro i hi
        obtain ⟨hiu, ht⟩ := (Finset.mem_filter.mp hi).2
        have hid : i ≠ d := by
          rintro rfl
          exact bad (by simpa [hdv] using ht)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hid, by simpa [g, hiu] using ht⟩
      · intro eq
        have hold : u ∉ good (u, f) := by simp [good]
        have hnew : u ∈ good (d, g) := by simp [good, g, Ne.symm hdu, htrue]
        exact hold (eq ▸ hnew)
    exact (Nat.not_lt_of_ge le) (Finset.card_lt_card strict)
  refine ⟨v, u, huv, htrue, f, ?_⟩
  intro c hc
  have hcu : c ≠ u := fun eq => hc (eq ▸ And.intro huv htrue)
  have hcd : c ≠ d := by
    rintro rfl
    exact hc ⟨hdv ▸ incident c hdu, hdtrue⟩
  refine ⟨incident c hcu, fun h => hcd (inj c d hcu hdu (h.trans hdv.symm)), ?_⟩
  intro e he heq
  exact inj c e hcu (fun eq => he (eq ▸ And.intro huv htrue)) heq

end DeficiencyOnePivot
