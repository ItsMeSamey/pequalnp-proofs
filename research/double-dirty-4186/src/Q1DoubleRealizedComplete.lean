import DDVirtualEvidence
import DDStarOriginal
import Q1DoubleTriangleCanonical
import DDOneLeakOriginal
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
open Virtual Q0.Factor
namespace OriginalCut
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
private theorem forgetLive {V : DAG} {u v : Node} (p : Relation.ReflTransGen V.liveStep u v) :
    Relation.ReflTransGen V.step u v := by
  induction p with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail last.1
theorem originPair (s : OriginalCut G C) {a g t : ℕ} (side : Fin 2)
    (pin : opnd C s.mixer side=n+a) (hg : g∈andRegion n C a) (ht : t∈s.exteriorOn g) :
    Root.arm side ∈s.dag.reaches g ∧ Root.ext t ∈s.dag.reaches g := by
  classical
  obtain ⟨ext,gt⟩ := Finset.mem_filter.mp ht
  obtain ⟨ne,ct⟩ := Finset.mem_erase.mp ext
  have top := (Finset.mem_filter.mp ct).1
  obtain ⟨H,_,uniq⟩ := unique_influenced_top s.double s.edge s.least s.form
  have same := uniq s.top ⟨(Finset.mem_filter.mp s.centrelessTop).1,s.influence⟩
  have off : ¬ Influence n C s.mixer (n+t) := fun h => ne ((uniq t ⟨top,h⟩).trans same.symm)
  obtain ⟨f,_,path,_,arm,external⟩ :=
    Virtual.realized_indexed_label s.double s.edge s.least s.form ((tops G C).erase s.top)
      (Finset.erase_subset _ _) (opnd C s.mixer) (n+s.top) side pin pin
      (Finset.mem_erase.mpr ⟨ne,top⟩) off hg (Finset.mem_of_mem_erase gt)
  have extend {r : Root} (reach : r∈s.dag.reaches f) : r∈s.dag.reaches g := by
    obtain ⟨member,tail⟩ := DAG.mem_reaches.mp reach
    exact DAG.mem_reaches.mpr ⟨member,(forgetLive path).trans tail⟩
  exact ⟨extend arm,extend external⟩
theorem armSingleRealized (s : OriginalCut G C) (P : CapRealization s) {a : ℕ} (b : Fin 2)
    (pin : opnd C s.mixer b = n+a) : s.ArmSingle a := by
  classical
  intro g hg
  by_contra! more
  obtain ⟨t,ht,u,hu,ne⟩ := Finset.one_lt_card.mp more
  obtain ⟨arm,xt⟩ := s.originPair b pin hg ht
  have xu := (s.originPair b pin hg hu).2
  have path := (DAG.mem_reaches.mp arm).2
  have paid : g∈s.dag.paidRows := by
    rcases Relation.ReflTransGen.cases_head path with impossible|⟨_,first,_⟩
    · cases impossible
    · exact first.1
  have sub : ({Root.arm b,Root.ext t,Root.ext u} : Finset Root) ⊆ s.dag.reaches g := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact arm
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact xt
    · exact (Finset.mem_singleton.mp hz) ▸ xu
  have bound := Finset.card_le_card sub
  have cap := P.rootCap paid
  simp [ne] at bound
  omega
theorem positiveRealized (s : OriginalCut G C) (P : CapRealization s) : Positive G C := by
  apply s.finish P.virtualEvidence s.completeSingleExternalLeak _ s.triangleEndpoint
  rintro (⟨many,empty⟩|⟨many,empty⟩)
  · exact s.completeOneArmMany s.left s.right (.inl ⟨rfl,rfl⟩) many empty
      (s.armSingleRealized P 0 (by simp [opnd,s.pins]))
  · exact s.completeOneArmMany s.right s.left (.inr ⟨rfl,rfl⟩) many empty
      (s.armSingleRealized P 1 (by simp [opnd,s.pins]))
end OriginalCut

theorem completeOfRealization
    (real : ∀ {n} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (s : OriginalCut G C), Nonempty (OriginalCut.CapRealization s)) : DoubleDirtyCase := by
  intro n G inst C four edge least form one witness
  obtain ⟨m,hm,a,ja,b,jb,pins⟩ := witness
  have d := doubleDirty_of_pins one hm ja jb pins
  obtain ⟨H,⟨ht,aff⟩,_⟩ := unique_influenced_top d edge least form
  let s : OriginalCut G C := ⟨m,a,b,H,d,four,edge,least,form,pins,ja,jb,
    (influenced_top_route d edge least form ht aff).1,aff⟩
  obtain ⟨P⟩ := real s
  exact s.positiveRealized P
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
