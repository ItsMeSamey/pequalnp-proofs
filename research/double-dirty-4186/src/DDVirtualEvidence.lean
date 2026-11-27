import Q1DoubleIndexedLabels
import DDIndexedInfluence
import DDRootReach
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
open Virtual
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

structure CapRealization (s : OriginalCut G C) where
  F : RootForest G C
  idx : Node → ℕ
  direct : ∀ i v, v ∈ s.dag.readers i → idx v ∈ readers n F.net (idx (.row i))
  valid : ∀ i ∈ s.dag.paidRows, idx (.row i) < F.net.size ∧ (gateAt F.net (idx (.row i))).op = .and
  root : ∀ r ∈ s.dag.roots, idx r.node ∈ F.roots
  distinct : Set.InjOn (fun r : Root => idx r.node) (s.dag.roots : Set Root)
  closed : F.Closed
  apart : ∀ r∈F.roots, ∀ t∈F.roots, ¬ F.Up r t

namespace CapRealization
variable {s : OriginalCut G C} (P : CapRealization s)

private theorem nonterminal {g : ℕ} (two : 2 ≤ (s.dag.reaches g).card)
    {r : Root} (hr : r ∈ s.dag.roots) : (.row g : Node) ≠ r.node := by
  intro e
  have sub : s.dag.reaches g ⊆ {r} := by
    intro t ht
    have p := (DAG.mem_reaches.mp ht).2
    rw [e] at p
    rcases Relation.ReflTransGen.cases_head p with eq | ⟨v,st,_⟩
    · exact Finset.mem_singleton.mpr (Root.node_injective eq).symm
    · exact (s.dag.terminal hr v st).elim
  have h := Finset.card_le_card sub
  simp at h
  omega

private theorem rootImage {g : ℕ} (two : 2 ≤ (s.dag.reaches g).card) :
    (s.dag.reaches g).image (fun r => P.idx r.node) ⊆ P.F.ends (P.idx (.row g)) := by
  intro i hi
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨rr,path⟩ := DAG.mem_reaches.mp hr
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with eq | strict
  · exact (nonterminal two rr eq.symm).elim
  · exact P.F.mem_ends.mpr ⟨P.root r rr,physical_strict P.direct strict⟩

private theorem imageCard (g : ℕ) :
    ((s.dag.reaches g).image (fun r => P.idx r.node)).card = (s.dag.reaches g).card :=
  Finset.card_image_of_injOn (fun _ ha _ hb => P.distinct (DAG.mem_reaches.mp ha).1 (DAG.mem_reaches.mp hb).1)

include P in
theorem rootCap {g : ℕ} (hg : g ∈ s.dag.paidRows) : (s.dag.reaches g).card ≤ 2 := by
  by_contra! gt
  have h := Finset.card_le_card (P.rootImage (g:=g) (by omega))
  rw [P.imageCard] at h
  have ⟨valid,andg⟩ := P.valid _ hg
  have := P.F.all_root_count s.least s.edge P.closed P.apart valid andg
  omega

private theorem exactImage {g : ℕ} (hg : g ∈ s.dag.paidRows) (h : (s.dag.reaches g).card=2) :
    (s.dag.reaches g).image (fun r => P.idx r.node) = P.F.ends (P.idx (.row g)) := by
  apply Finset.eq_of_subset_of_card_le (P.rootImage (by omega))
  rw [P.imageCard,h]
  exact P.F.all_root_count s.least s.edge P.closed P.apart (P.valid _ hg).1 (P.valid _ hg).2

include P in
theorem virtualEvidence : s.VirtualEvidence := by
  classical
  have rep (side : Fin 2) {a : ℕ} (pin : opnd C s.mixer side=n+a) :
      Represents s.dag (externalLabels G C s.top a) side := by
    intro t ht
    obtain ⟨g,hg,_,ha,he⟩ := s.forkOfLabel side pin ht
    refine ⟨g,hg,?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · exact h.symm ▸ ha
      · exact (Finset.mem_singleton.mp h).symm ▸ he
    · simpa using P.rootCap hg
  refine ⟨s.dag,rep 0 (by simp [opnd,s.pins]),rep 1 (by simp [opnd,s.pins]),?_⟩
  intro i hi j hj _ ti tj
  have ei := P.exactImage hi ti
  have ej := P.exactImage hj tj
  have pi : 2 ≤ (P.F.ends (P.idx (.row i))).card := by rw [←ei,P.imageCard,ti]
  have pj : 2 ≤ (P.F.ends (P.idx (.row j))).card := by rw [←ej,P.imageCard,tj]
  obtain ⟨z,hz⟩ := P.F.pairwise_intersection s.least s.edge P.closed P.apart
    (P.valid i hi).1 (P.valid i hi).2 pi (P.valid j hj).1 (P.valid j hj).2 pj
  rw [←ei,←ej] at hz
  obtain ⟨li,lj⟩ := Finset.mem_inter.mp hz
  obtain ⟨r,hr,er⟩ := Finset.mem_image.mp li
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp lj
  have same : r=q := P.distinct (DAG.mem_reaches.mp hr).1 (DAG.mem_reaches.mp hq).1 (er.trans eq.symm)
  exact ⟨r,Finset.mem_inter.mpr ⟨hr,by simpa only [same] using hq⟩⟩
end CapRealization
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
