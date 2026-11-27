import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q0Partition

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped BigOperators

/-- Follow a dirty gate's reader until the first centreless top. -/
inductive EndsAt (step : ℕ → ℕ → Prop) (terminal : ℕ → Prop) : ℕ → ℕ → Prop
  | stop {a} (h : terminal a) : EndsAt step terminal a a
  | next {a b t} (ha : ¬ terminal a) (hab : step a b)
      (tail : EndsAt step terminal b t) : EndsAt step terminal a t

theorem end_unique {step : ℕ → ℕ → Prop} {terminal : ℕ → Prop}
    (uniqueReader : ∀ {a b d}, step a b → step a d → b = d)
    {a s t} (hs : EndsAt step terminal a s) (ht : EndsAt step terminal a t) : s = t := by
  induction hs generalizing t with
  | stop h =>
    cases ht with
    | stop => rfl
    | next hn _ _ => exact (hn h).elim
  | next hn hab tail ih =>
    cases ht with
    | stop h => exact (hn h).elim
    | next _ had rest =>
      obtain rfl := uniqueReader hab had
      exact ih rest

/-- Edges may be captured by several tops. Only the dirty-gate charges need disjointness. -/
theorem charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (edges : ℕ → Finset (Sym2 (Fin n))) (dirty : ℕ → Finset ℕ)
    (covered : Ustar G C ⊆ (centreless G C).biUnion edges)
    (realDirty : ∀ t ∈ centreless G C, dirty t ⊆ junk G C)
    (uniqueOwner : ∀ a ∈ centreless G C, ∀ b ∈ centreless G C,
      ∀ d ∈ dirty a, d ∈ dirty b → a = b)
    (perTop : ∀ t ∈ centreless G C, 2 * (edges t).card ≤ (dirty t).card + 2) :
    2 * (Ustar G C).card ≤ (junk G C).card + 2 * (centreless G C).card := by
  classical
  have hd : ((centreless G C) : Set ℕ).PairwiseDisjoint dirty := by
    intro a ha b hb hab
    exact Finset.disjoint_left.mpr fun d hda hdb => hab (uniqueOwner a ha b hb d hda hdb)
  have hsub : (centreless G C).biUnion dirty ⊆ junk G C := by
    intro d hd'
    obtain ⟨t, ht, hdt⟩ := Finset.mem_biUnion.mp hd'
    exact realDirty t ht hdt
  have counted : (∑ t ∈ centreless G C, (dirty t).card) ≤ (junk G C).card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsub
  have he : (Ustar G C).card ≤ ∑ t ∈ centreless G C, (edges t).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  calc
    2 * (Ustar G C).card ≤ 2 * (∑ t ∈ centreless G C, (edges t).card) := Nat.mul_le_mul_left _ he
    _ = ∑ t ∈ centreless G C, 2 * (edges t).card := Finset.mul_sum ..
    _ ≤ ∑ t ∈ centreless G C, ((dirty t).card + 2) := Finset.sum_le_sum perTop
    _ = (∑ t ∈ centreless G C, (dirty t).card) + 2 * (centreless G C).card := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_right counted _

/-- Reader determinism supplies the ownership condition on the concrete gate cones. -/
theorem charge_of_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (edges : ℕ → Finset (Sym2 (Fin n))) (dirty : ℕ → Finset ℕ)
    (covered : Ustar G C ⊆ (centreless G C).biUnion edges)
    (realDirty : ∀ t ∈ centreless G C, dirty t ⊆ junk G C)
    (uniqueReader : ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b)
    (routes : ∀ t ∈ centreless G C, ∀ d ∈ dirty t,
      EndsAt (fun i j => i ∈ junk G C ∧ j ∈ readers n C i)
        (fun i => i ∈ centreless G C) d t)
    (perTop : ∀ t ∈ centreless G C, 2 * (edges t).card ≤ (dirty t).card + 2) :
    2 * (Ustar G C).card ≤ (junk G C).card + 2 * (centreless G C).card := by
  apply charge G C edges dirty covered realDirty _ perTop
  intro a ha b hb d hda hdb
  apply end_unique (hs := routes a ha d hda) (ht := routes b hb d hdb)
  intro i j k hj hk
  exact uniqueReader i hj.1 j hj.2 k hk.2

end PEqualNP.Outside.L_meta_4186_aux.Q0Partition
