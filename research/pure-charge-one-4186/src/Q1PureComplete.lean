import Q1CoverUnion
import Q1LocalCover
import Q1PureFactor
import Q1PureFrontier
import Q1PureSupport
import Q1PureStar

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0
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

private theorem children_stars {n e : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pe : PureException G C e) (four : NoFourCycle G) (least : IsLeastAO G C) :
    clauseStars G C {orIn n C (opnd C e 0), orIn n C (opnd C e 1)} := by
  intro K hk p hp q hq ne
  have one (b : Fin 2) (eq : K = orIn n C (opnd C e b)) : Anchored G C K := by
    rcases child_pin_alternative pe four least b with small | anch
    · rw [← eq] at small
      exact (ne (Finset.card_le_one.mp small p hp q hq)).elim
    · simpa only [eq] using anch
  rcases Finset.mem_insert.mp hk with eq | eq
  · exact one 0 eq
  · exact one 1 (Finset.mem_singleton.mp eq)

theorem complete_of_pureException {n e : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (pe : PureException G C e) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card := by
  classical
  have nd : NoDirtyOr G C := pe.noDirtyOr least.1
  apply cover_of_routed_local_covers G C four edge least form (Q1Pure.unique_reader G C edge least form nd)
  · intro t ht hn u v _ hv
    exact Q1Pure.noncentreless_accepted_star least.1 form nd (Finset.mem_sdiff.mpr ⟨ht,hn⟩) u v hv
  · intro H hH
    obtain ⟨F, cost, sem, raw⟩ := Q1Pure.routed_frontier least.1 form nd hH
    let R := Ustar G C ∩ gammaE G C H
    let clauses := F.image (orIn n C)
    have cap : ∀ a b, s(a,b) ∈ R → hitsPair clauses a b ∧ s(a,b) ∈ Ustar G C := by
      intro a b he
      obtain ⟨r,g⟩ := Finset.mem_inter.mp he
      exact ⟨gamma_hits sem g, r⟩
    have top : H ∈ tops G C := (Finset.mem_filter.mp hH).1
    have below : BelowF G C H := (Finset.mem_filter.mp top).2.2
    have clean (x y : Fin n) (hit : hitsPair clauses x y) : G.Adj x y := by
      apply (S4183.S90.graphFun_pair G x y).mp
      apply below (pairInput x y)
      apply (sem _).mpr
      intro K hK
      rcases hit K hK with hx | hy
      · exact ⟨x,hx,by simp [pairInput]⟩
      · exact ⟨y,hy,by simp [pairInput]⟩
    have stars := frontier_clauseStars_erase pe four least F raw
    exact local_cover R cap four stars below sem cost (routedJunk_pos least.1 form nd hH)
      (fork_of_children four stars clean (exceptional_union pe least.1) (children_stars pe four least) R cap)

theorem complete {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (q : (orN G C \ lam G C).card = 1)
    (pure : ∃ e ∈ orN G C \ lam G C, ∀ j, InCone n C j e → (gateAt C j).op = GateOp.or) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card := by
  obtain ⟨e, he, cone⟩ := pure
  exact complete_of_pureException G C four edge least form (pureException_of_card q he cone)

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
