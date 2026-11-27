import Q1Matching
import Q1Nonmatching
import Q0Transversal

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

private theorem matching_charge {n H d : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {clauses : Finset (Finset (Fin n))} {exc : Finset (Fin n)} (E : Finset (Sym2 (Fin n)))
    (residual : E ⊆ Ustar G C)
    (accepted : ∀ e ∈ E, ∀ a b, e = s(a,b) → hitsPair clauses a b)
    (noFork : ∀ h u v, s(h,u) ∈ E → s(h,v) ∈ E → u = v)
    (four : NoFourCycle G) (stars : clauseStars G C (clauses.erase exc)) (below : BelowF G C H)
    (sem : ∀ x, gateVal n C H x = true ↔ ∀ K ∈ clauses, ∃ a ∈ K, x a = true)
    (bound : clauses.card ≤ d + 2) : 2 * E.card ≤ d + 2 := by
  classical
  have clean (a b : Fin n) (hit : hitsPair clauses a b) : G.Adj a b := by
    have hg := below (pairInput a b) ((sem _).mpr (by
      intro K hK
      rcases hit K hK with ha | hb
      · exact ⟨a, ha, by simp [pairInput]⟩
      · exact ⟨b, hb, by simp [pairInput]⟩))
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pairInput] at hg
    obtain ⟨u,v,adj,hu,hv⟩ := hg
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.irrefl adj).elim
    · exact adj
    · exact adj.symm
    · exact (G.irrefl adj).elim
  let enum := E.equivFin.symm
  have repr (i : Fin E.card) : ∃ a b, (enum i).val = s(a,b) := by
    exact Sym2.inductionOn (enum i).val (fun a b => ⟨a,b,rfl⟩)
  choose a b hab using repr
  let pt (i : Fin E.card) (k : Bool) := if k then b i else a i
  have orient (i : Fin E.card) (k : Bool) : (enum i).val = s(pt i k, pt i (!k)) := by
    cases k
    · exact hab i
    · exact (hab i).trans Sym2.eq_swap
  have hit (i : Fin E.card) (k : Bool) : hitsPair clauses (pt i k) (pt i (!k)) :=
    accepted _ (enum i).property _ _ (orient i k)
  have resid (i : Fin E.card) (k : Bool) : s(pt i k, pt i (!k)) ∈ Ustar G C :=
    orient i k ▸ residual (enum i).property
  have sep {i j : Fin E.card} (ij : i ≠ j) (k l : Bool) : pt i k ≠ pt j l := by
    intro eq
    have ei : s(pt i k, pt i (!k)) ∈ E := orient i k ▸ (enum i).property
    have ej : s(pt j l, pt j (!l)) ∈ E := orient j l ▸ (enum j).property
    have other := noFork (pt i k) (pt i (!k)) (pt j (!l)) ei (eq ▸ ej)
    apply ij
    apply enum.injective
    apply Subtype.ext
    rw [orient i k, orient j l, eq, other]
  apply Q0Transversal.local_charge (K := ↥clauses) pt (fun K z => z ∈ K.val)
  · intro K i
    exact hit i false K.val K.property
  · intro t
    let x (z : Fin n) := decide (∃ i, pt i (t i) = z)
    by_contra! denies
    have act := (sem x).mpr (by
      intro K hK
      obtain ⟨i, hi⟩ := denies (⟨K,hK⟩ : ↥clauses)
      exact ⟨_, hi, decide_eq_true ⟨i,rfl⟩⟩)
    have ge := below x act
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, x] at ge
    obtain ⟨u,v,adj,⟨i,rfl⟩,⟨j,rfl⟩⟩ := ge
    by_cases ij : i = j
    · subst j; exact G.irrefl adj
    · exact Q1Pure.matching_induced four stars clean (hit i (t i)) (hit j (t j))
        (resid i (t i)) (resid j (t j)) (sep ij _ _) (sep ij _ _)
        (sep (Ne.symm ij) _ _) (sep ij _ _) adj
  · simpa using bound

/-- Choose a local cover of the accepted residuals at one top. A shared endpoint
uses the two-edge-star classification; vertex-disjoint edges use transversals. -/
theorem local_cover {n H d : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {clauses : Finset (Finset (Fin n))} {exc : Finset (Fin n)}
    (R : Finset (Sym2 (Fin n)))
    (capture : ∀ a b, s(a,b) ∈ R → hitsPair clauses a b ∧ s(a,b) ∈ Ustar G C)
    (four : NoFourCycle G) (stars : clauseStars G C (clauses.erase exc))
    (below : BelowF G C H)
    (sem : ∀ x, gateVal n C H x = true ↔ ∀ K ∈ clauses, ∃ a ∈ K, x a = true)
    (bound : clauses.card ≤ d + 2) (hd : 0 < d)
    (collapse : ∀ h u v, u ≠ v → s(h,u) ∈ R → s(h,v) ∈ R → R = {s(h,u),s(h,v)}) :
    ∃ V : Finset (Fin n), (∀ u v, s(u,v) ∈ R → u ∈ V ∨ v ∈ V) ∧ V.card + R.card ≤ d+2 := by
  classical
  by_cases fork : ∃ h u v, u ≠ v ∧ s(h,u) ∈ R ∧ s(h,v) ∈ R
  · obtain ⟨h,u,v,ne,hu,hv⟩ := fork
    obtain ⟨covers,card,cost⟩ := fork_cover_cost (collapse h u v ne hu hv) ne d hd
    exact ⟨{h}, covers, card.le.trans cost⟩
  · have noFork (h u v : Fin n) (hu : s(h,u) ∈ R) (hv : s(h,v) ∈ R) : u = v := by
      by_contra ne
      exact fork ⟨h,u,v,ne,hu,hv⟩
    have res : R ⊆ Ustar G C := by
      intro e
      induction e using Sym2.inductionOn with
      | _ a b => exact fun h => (capture a b h).2
    have boundR := matching_charge R res (fun e he a b eq => (capture a b (eq ▸ he)).1)
      noFork four stars below sem bound
    let V := R.image (fun e : Sym2 (Fin n) => e.out.1)
    have hv : V.card ≤ R.card := Finset.card_image_le
    refine ⟨V, ?_, by omega⟩
    intro u v he
    have hp : (s(u,v)).out.1 ∈ V := Finset.mem_image.mpr ⟨_,he,rfl⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u,v)) with eq | eq
    · exact Or.inl (eq ▸ hp)
    · exact Or.inr (eq ▸ hp)

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
