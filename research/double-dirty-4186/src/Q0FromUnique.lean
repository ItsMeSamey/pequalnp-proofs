import Q0Routes
import Q0Star
import Q0Misses
import Q0CoverBound
import Q0ClauseStars
import Q0ClauseRegion

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

private theorem gamma_hits {n H : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {clauses : Finset (Finset (Fin n))}
    (sem : ∀ x, gateVal n C H x = true ↔ ∀ K ∈ clauses, ∃ a ∈ K, x a = true)
    {a b : Fin n} (h : s(a,b) ∈ gammaE G C H) : hitsPair clauses a b := by
  obtain ⟨_, u, v, same, active⟩ := Finset.mem_filter.mp h
  have sets : pairInput u v = pairInput a b := by
    rcases Sym2.eq_iff.mp same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · funext w
      simp [pairInput, or_comm]
  rw [sets] at active
  intro K hK
  obtain ⟨z, hz, h⟩ := (sem _).mp active K hK
  rcases (Q0ReaderDeps.S90.pairInput_true a b z).mp h with rfl | rfl
  · exact Or.inl hz
  · exact Or.inr hz

theorem from_unique_and_clauses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (hq : (orN G C \ lam G C).card = 0)
    (uniqueReader : ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b)
    (primitive : ∀ H ∈ centreless G C, ∃ clauses : Finset (Finset (Fin n)),
      clauses.card ≤ (routedJunk n G C H).card + 2 ∧
      (∀ x, gateVal n C H x = true ↔ ∀ A ∈ clauses, ∃ a ∈ A, x a = true) ∧
      clauseStars G C clauses) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  classical
  apply endpointOfCharge G C four edge least form
  apply Q0Partition.charge_of_readers G C (fun H => Ustar G C ∩ gammaE G C H) (routedJunk n G C)
  · apply residual_gamma_cover least
    intro t ht hnc u v _ hv
    exact noncentreless_accepted_star least.1 form hq (Finset.mem_sdiff.mpr ⟨ht,hnc⟩) u v hv
  · intro t _ d hd
    exact (mem_routedJunk.mp hd).1
  · exact uniqueReader
  · intro t _ d hd
    exact (mem_routedJunk.mp hd).2
  · intro H hH
    obtain ⟨K, bound, sem, stars⟩ := primitive H hH
    have top : H ∈ tops G C := (Finset.mem_filter.mp hH).1
    have below : BelowF G C H := (Finset.mem_filter.mp top).2.2
    apply residual_local_charge _ Finset.inter_subset_left _ four stars below sem bound
    rintro e he a b rfl
    exact gamma_hits sem (Finset.mem_inter.mp he).2

theorem from_unique_and_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (hq : (orN G C \ lam G C).card = 0)
    (uniqueReader : ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b)
    (primitive : ∀ H ∈ centreless G C, ∃ F : Finset ℕ,
      (F.image (orIn n C)).card ≤ (routedJunk n G C H).card + 2 ∧
      (∀ x, gateVal n C H x = true ↔ ∀ A ∈ F.image (orIn n C), ∃ a ∈ A, x a = true) ∧
      (∀ w ∈ F, w < n ∨ ∃ k < C.gates.length, w = n+k ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or)) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  apply from_unique_and_clauses G C four edge least form hq uniqueReader
  intro H ht
  obtain ⟨F, bound, sem, raw⟩ := primitive H ht
  exact ⟨_, bound, sem, frontierClauseStars four least hq F raw⟩

theorem from_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (hq : (orN G C \ lam G C).card = 0)
    (uniqueReader : ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card :=
  from_unique_and_frontier G C four edge least form hq uniqueReader
    (fun _ ht => routed_frontier least.1 form hq ht)

end PEqualNP.Outside.L_meta_4186_aux.Q0
