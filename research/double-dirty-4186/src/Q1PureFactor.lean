import Q1PureRoutes
import Q1PureCost
import Q1PurePins
import Q0FactorActual

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q0ReaderDeps S4183.S98
open Q0.Factor

theorem affected_top_of_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : NoDirtyOr G C) (hg : g ∈ junk G C)
    (affected : ℕ → Bool) (start : affected g = true)
    (follow : ∀ {a b}, a ∈ junk G C → b ∈ readers n C a →
      affected a = true → affected b = true) :
    ∃ t ∈ tops G C, affected t = true := by
  obtain ⟨t, ht, path⟩ := Q1Pure.some_dirty_route edge least hq g hg
  have walk {i j : ℕ} (p : DirtyRoute n G C i j) : affected i = true → affected j = true := by
    induction p with
    | stop => exact id
    | next _ hab _ ih => exact fun h => ih (follow hab.1 hab.2 h)
  exact ⟨t, (Finset.mem_filter.mp ht).1, walk path start⟩

theorem some_affected_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : NoDirtyOr G C) (hg : g ∈ junk G C) :
    ∃ t ∈ tops G C, affected n C g t = true := by
  classical
  apply affected_top_of_readers G C g edge least hq hg
  · simpa [affected] using (AndPath.source : AndPath n C g (n+g))
  · intro a b ha hb prev
    obtain ⟨bound, pin⟩ := Finset.mem_filter.mp hb
    have lt := Finset.mem_range.mp bound
    have notOr := hq ha lt pin
    have andOp := (least.1.1 _ (PEqualNP.Outside.L_meta_4186_aux.Q0ReaderDeps.S90.gateAt_mem lt)).resolve_right notOr
    have path : AndPath n C g (n+a) := by simpa [affected] using prev
    simpa [affected] using (AndPath.step path lt andOp pin)

/-- The cost, route and list arguments use concrete circuit rows; only the value
invariant of that same row traversal is needed at this interface. -/
theorem two_readers_contradiction_of_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : NoDirtyOr G C)
    (hg : g ∈ junk G C) (two : 2 ≤ (readers n C g).card)
    (source : ∀ B : Bank n, Good B (doneLayout G C g) → B (gateVal n C g))
    (sem : ∀ t ∈ tops G C, ∀ x, gateVal n C t x =
      (if affected n C g t then gateVal n C g x && denotation (readPin (doneLayout G C g) (n+t)) x
       else denotation (readPin (doneLayout G C g) (n+t)) x)) : False := by
  obtain ⟨D, ao, same, short⟩ := actual_competitor G C g (Q1Pure.row_savings least.1 hq hg) two (by
    intro B good
    have dirty := ((PEqualNP.Outside.L_meta_4186_aux.S4183.junk_iff G C g).mp hg).2.2
    exact join_from_top_slots G C g edge least form dirty (affected n C g) _ B (source B good)
      (some_affected_top G C g edge least hq hg) (fun t _ => read_good good (n+t)) sem)
  exact (Nat.not_le_of_gt short) (least.2.2 D ao same)

theorem unique_reader_of_pinRules {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : NoDirtyOr G C)
    (rules : ∀ g ∈ junk G C, PinRules G C g) :
    ∀ g ∈ junk G C, ∀ a ∈ readers n C g, ∀ b ∈ readers n C g, a = b := by
  apply readers_equal_of_card_obstruction G C
  intro g hg two
  obtain ⟨source, sem⟩ := top_wire_semantics G C g least.1 hg (rules g hg)
  exact two_readers_contradiction_of_semantics G C g edge least form hq hg two source sem

theorem unique_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : NoDirtyOr G C) :
    ∀ g ∈ junk G C, ∀ a ∈ readers n C g, ∀ b ∈ readers n C g, a = b :=
  unique_reader_of_pinRules G C edge least form hq (fun g hg => Q1Pure.pinRules G C g edge least form hq hg)

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
