import Q1DoubleResidual
import Q1DoubleShapes
import Q1DoubleLedger

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

structure Allocation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) where
  components : Finset ℕ
  pivot : ℕ
  dirty : ℕ → Finset ℕ
  roots : ℕ → Finset ℕ
  edges : ℕ → Finset (Sym2 (Fin n))
  dirtySub : ∀ i ∈ components, dirty i ⊆ junk G C
  rootSub : ∀ i ∈ components, roots i ⊆ centreless G C
  dirtyDisj : (components : Set ℕ).PairwiseDisjoint dirty
  rootDisj : (components : Set ℕ).PairwiseDisjoint roots
  covers : Ustar G C ⊆ components.biUnion edges

namespace Allocation

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def Local (A : Allocation G C) (i : ℕ) : Prop :=
  ∃ V : Finset (Fin n), (∀ u v, s(u,v) ∈ A.edges i → u ∈ V ∨ v ∈ V) ∧
    V.card + (A.edges i).card ≤ (A.dirty i).card + 2 * (A.roots i).card +
      (if i = A.pivot then 1 else 0)

theorem localOfSelection (A : Allocation G C) (i : ℕ) (pick : Sym2 (Fin n) → Fin n)
    (incident : ∀ e ∈ A.edges i, pick e ∈ e)
    (size : ((A.edges i).image pick).card + (A.edges i).card ≤
      (A.dirty i).card + 2*(A.roots i).card + (if i = A.pivot then 1 else 0)) : A.Local i := by
  refine ⟨_, ?_, size⟩
  intro u v he
  have hmem := Finset.mem_image_of_mem pick he
  rcases Sym2.mem_iff.mp (incident s(u,v) he) with h | h
  · exact Or.inl (h ▸ hmem)
  · exact Or.inr (h ▸ hmem)

theorem localOfAmple (A : Allocation G C) (i : ℕ)
    (size : 2*(A.edges i).card ≤ (A.dirty i).card + 2*(A.roots i).card +
      (if i = A.pivot then 1 else 0)) : A.Local i := by
  classical
  apply A.localOfSelection i (fun e => e.out.1) (fun e _ => Sym2.out_fst_mem e)
  have h : ((A.edges i).image (fun e : Sym2 (Fin n) => e.out.1)).card ≤ (A.edges i).card :=
    Finset.card_image_le
  omega

theorem finish (A : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (paid : ∀ i ∈ A.components, A.Local i) : Positive G C := by
  unfold Positive
  rw [one]
  exact component_cover G C four edge least form A.components A.pivot A.dirty A.roots A.edges
    A.dirtySub A.rootSub A.dirtyDisj A.rootDisj A.covers paid

end Allocation

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
