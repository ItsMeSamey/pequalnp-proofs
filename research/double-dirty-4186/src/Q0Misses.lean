import Q0Matching
import Q0Transversal

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

theorem residual_local_charge {n H d : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {clauses : Finset (Finset (Fin n))} (E : Finset (Sym2 (Fin n)))
    (residual : E ⊆ Ustar G C)
    (accepted : ∀ e ∈ E, ∀ a b, e = s(a,b) → hitsPair clauses a b)
    (four : NoFourCycle G) (stars : clauseStars G C clauses) (below : BelowF G C H)
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
    have hj : hitsPair clauses (pt i k) (pt j (!l)) := eq ▸ hit j l
    have other := matching_unique four stars clean (hit i k) hj (resid i k)
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
    · exact matching_induced four stars clean (hit i (t i)) (hit j (t j))
        (resid i (t i)) (resid j (t j)) (sep ij _ _) (sep ij _ _)
        (sep (Ne.symm ij) _ _) (sep ij _ _) adj
  · simpa using bound

end PEqualNP.Outside.L_meta_4186_aux.Q0
