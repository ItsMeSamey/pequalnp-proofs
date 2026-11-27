import Q1PrivateBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q0

/-- Construct an actual indexed batch from an owned edge set and projected
clause occurrences; separation and inducedness follow from the graph hypotheses. -/
theorem batch_of_owned {n a w : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (A : Fin a → Clause n) (W : Fin w → Clause n)
    (R : Finset (Sym2 (Fin n))) (remain : R ⊆ Ustar G C)
    (hit : ∀ u v, s(u,v) ∈ R → ∀ c, u ∈ literals A W c ∨ v ∈ literals A W c)
    (clean : ∀ S : Finset (Fin n), (∀ c, ∃ v ∈ S, v ∈ literals A W c) →
      ∃ x ∈ S, ∃ y ∈ S, G.Adj x y)
    (anchor : ∀ c, ∀ x ∈ literals A W c, ∀ y ∈ literals A W c, x ≠ y →
      ∃ d, ∀ z ∈ literals A W c, G.Adj d z ∧ s(d,z) ∈ starEdges G C) :
    ∃ P : Batch G C A W R.card, ∀ i, (R.equivFin.symm i).val = s(P.pt i false,P.pt i true) := by
  classical
  let cls := Finset.univ.image (literals A W)
  have stars : clauseStars G C cls := by
    intro K hk
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hk
    exact anchor c
  have cleanPair (u v : Fin n) (hu : hitsPair cls u v) : G.Adj u v := by
    obtain ⟨x,hx,y,hy,adj⟩ := clean {u,v} (by
      intro c
      have h := hu _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))
      rcases h with h | h
      · exact ⟨u,by simp,h⟩
      · exact ⟨v,by simp,h⟩)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (G.irrefl adj).elim
    · exact adj
    · exact adj.symm
    · exact (G.irrefl adj).elim
  let en := R.equivFin.symm
  have ex (i : Fin R.card) : ∃ x y, (en i).val=s(x,y) :=
    Sym2.inductionOn (en i).val (fun x y => ⟨x,y,rfl⟩)
  choose x y exy using ex
  let p (i : Fin R.card) (b : Bool) := if b then y i else x i
  have repr (i) (b : Bool) : (en i).val=s(p i b,p i (!b)) := by
    cases b
    · exact exy i
    · exact (exy i).trans Sym2.eq_swap
  have mem (i) (b : Bool) : s(p i b,p i (!b)) ∈ R := repr i b ▸ (en i).property
  have hp (i) (b : Bool) : hitsPair cls (p i b) (p i (!b)) := by
    intro K hK
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hK
    exact hit _ _ (mem i b) c
  have sep (i j : Fin R.card) (ne : i ≠ j) (b d : Bool) : p i b ≠ p j d := by
    intro eq
    have hn := Q0.matching_unique four stars cleanPair (hp i b) (eq ▸ hp j d) (remain (mem i b))
    apply ne
    apply en.injective
    apply Subtype.ext
    rw [repr i b,repr j d,eq,hn]
  refine ⟨⟨p,fun i b => cleanPair _ _ (hp i b), fun i b => remain (mem i b), sep, ?_,
    fun c i => hit _ _ (mem i false) c, clean, anchor⟩,fun i => repr i false⟩
  intro i j ne b d
  exact Q0.matching_induced four stars cleanPair (hp i b) (hp j d)
    (remain (mem i b)) (remain (mem j d)) (sep i j ne b d) (sep i j ne (!b) d)
    (sep j i ne.symm (!d) b) (sep i j ne (!b) (!d))

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
