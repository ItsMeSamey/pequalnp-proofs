import Q0FactorRows
import Q0Routes
import Q0FactorJoin
import Q0FactorCost
import Q0FactorPinRules

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem actual_competitor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ)
    (budget : expense (seed n) (rowsOf G C g) + (readers n C g).card + (orT G C).card ≤ C.size)
    (two : 2 ≤ (readers n C g).card)
    (decompose : ∀ B : Bank n, Good B (doneLayout G C g) →
      ∃ first : Signal n, ∃ affected unaffected : List (Signal n),
        B (gateVal n C g) ∧ B first ∧
        (∀ s ∈ affected, B s) ∧ (∀ s ∈ unaffected, B s) ∧
        combined (gateVal n C g) first affected unaffected = graphFun G ∅ ∧
        affected.length + unaffected.length = (orT G C).card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size < C.size := by
  obtain ⟨B, trace, good⟩ := compile (n := n) (rowsOf G C g)
  obtain ⟨first, affected, unaffected, hg, hf, ha, hu, hfuns, hc⟩ := decompose B good
  obtain ⟨D, hD, eqD, sizeD⟩ := circuit trace (gateVal n C g) first affected unaffected hg hf ha hu
  exact ⟨D, hD, eqD.trans hfuns, by omega⟩

theorem affected_top_of_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : (orN G C \ lam G C).card = 0) (hg : g ∈ junk G C)
    (affected : ℕ → Bool) (start : affected g = true)
    (follow : ∀ {a b}, a ∈ junk G C → b ∈ readers n C a →
      affected a = true → affected b = true) :
    ∃ t ∈ tops G C, affected t = true := by
  obtain ⟨t, ht, path⟩ := some_dirty_route edge least hq g hg
  have walk {i j : ℕ} (p : DirtyRoute n G C i j) : affected i = true → affected j = true := by
    induction p with
    | stop => exact id
    | next _ hab _ ih => exact fun h => ih (follow hab.1 hab.2 h)
  exact ⟨t, (Finset.mem_filter.mp ht).1, walk path start⟩

theorem some_affected_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : (orN G C \ lam G C).card = 0) (hg : g ∈ junk G C) :
    ∃ t ∈ tops G C, affected n C g t = true := by
  classical
  apply affected_top_of_readers G C g edge least hq hg
  · simpa [affected] using (AndPath.source : AndPath n C g (n+g))
  · intro a b ha hb prev
    obtain ⟨bound, pin⟩ := Finset.mem_filter.mp hb
    have lt := Finset.mem_range.mp bound
    have notOr := dirty_reader_not_or least.1 hq ha lt pin
    have andOp := (least.1.1 _ (PEqualNP.Outside.L_meta_4186_aux.Q0ReaderDeps.S90.gateAt_mem lt)).resolve_right notOr
    have path : AndPath n C g (n+a) := by simpa [affected] using prev
    simpa [affected] using (AndPath.step path lt andOp pin)

/-- The cost, route and list arguments use concrete circuit rows; only the value
invariant of that same row traversal is needed at this interface. -/
theorem two_readers_contradiction_of_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : (orN G C \ lam G C).card = 0)
    (hg : g ∈ junk G C) (two : 2 ≤ (readers n C g).card)
    (source : ∀ B : Bank n, Good B (doneLayout G C g) → B (gateVal n C g))
    (sem : ∀ t ∈ tops G C, ∀ x, gateVal n C t x =
      (if affected n C g t then gateVal n C g x && denotation (readPin (doneLayout G C g) (n+t)) x
       else denotation (readPin (doneLayout G C g) (n+t)) x)) : False := by
  obtain ⟨D, ao, same, short⟩ := actual_competitor G C g (row_savings least.1 hq hg) two (by
    intro B good
    have dirty := ((PEqualNP.Outside.L_meta_4186_aux.S4183.junk_iff G C g).mp hg).2.2
    exact join_from_top_slots G C g edge least form dirty (affected n C g) _ B (source B good)
      (some_affected_top G C g edge least hq hg) (fun t _ => read_good good (n+t)) sem)
  exact (Nat.not_le_of_gt short) (least.2.2 D ao same)

theorem readers_equal_of_card_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (obstruction : ∀ d ∈ junk G C, 2 ≤ (readers n C d).card → False) :
    ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b := by
  intro d hd a ha b hb
  by_contra neq
  exact obstruction d hd (Finset.one_lt_card.mpr ⟨a, ha, b, hb, neq⟩)

theorem unique_reader_of_pinRules {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : (orN G C \ lam G C).card = 0)
    (rules : ∀ g ∈ junk G C, PinRules G C g) :
    ∀ g ∈ junk G C, ∀ a ∈ readers n C g, ∀ b ∈ readers n C g, a = b := by
  apply readers_equal_of_card_obstruction G C
  intro g hg two
  obtain ⟨source, sem⟩ := top_wire_semantics G C g least.1 hg (rules g hg)
  exact two_readers_contradiction_of_semantics G C g edge least form hq hg two source sem

theorem unique_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : (orN G C \ lam G C).card = 0) :
    ∀ g ∈ junk G C, ∀ a ∈ readers n C g, ∀ b ∈ readers n C g, a = b :=
  unique_reader_of_pinRules G C edge least form hq (fun g hg => pinRules G C g edge least form hq hg)

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
