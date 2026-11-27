import Q1DoublePrivateLayoutGroup
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
structure OriginalCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) where
  mixer : ℕ
  left : ℕ
  right : ℕ
  top : ℕ
  double : DoubleDirty G C mixer
  four : NoFourCycle G
  edge : G.edgeFinset.Nonempty
  least : IsLeastAO G C
  form : PEqualNP.TopForm.TopForm G C
  pins : (gateAt C mixer).inputs=[n+left,n+right]
  leftDirty : left∈junk G C
  rightDirty : right∈junk G C
  centrelessTop : top∈centreless G C
  influence : Influence n C mixer (n+top)

namespace OriginalCut
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
noncomputable abbrev L (s : OriginalCut G C) := externalLabels G C s.top s.left
noncomputable abbrev R (s : OriginalCut G C) := externalLabels G C s.top s.right
def VirtualEvidence (s : OriginalCut G C) : Prop :=
  ∃ V : Virtual.DAG, Represents V s.L 0 ∧ Represents V s.R 1 ∧
    ∀ i∈V.paidRows, ∀ j∈V.paidRows, i≠j → (V.reaches i).card=2 → (V.reaches j).card=2 →
      ((V.reaches i) ∩ (V.reaches j)).Nonempty
def SingleEndpoint (s : OriginalCut G C) : Prop :=
  ∀ t, ((s.L={t} ∧ s.R=∅) ∨ (s.R={t} ∧ s.L=∅)) → Positive G C
def StarEndpoint (s : OriginalCut G C) : Prop :=
  ((2≤s.L.card ∧ s.R=∅) ∨ (2≤s.R.card ∧ s.L=∅)) → Positive G C
def TriangleEndpoint (s : OriginalCut G C) : Prop :=
  ∀ t, s.L={t} → s.R={t} → Positive G C

theorem finish (s : OriginalCut G C) (v : s.VirtualEvidence)
    (single : s.SingleEndpoint) (star : s.StarEndpoint) (triangle : s.TriangleEndpoint) : Positive G C := by
  obtain ⟨V,l,r,meet⟩ := v
  exact dispatchPhysical s.double s.four s.edge s.least s.form s.pins s.leftDirty s.rightDirty
    s.centrelessTop s.influence (classifyPhysical V l r meet) single star triangle
end OriginalCut

/-- Conditional assembly of the issued case, with four explicit branch obligations. -/
theorem assembleDoubleDirty
    (evidence : ∀ {n} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (s : OriginalCut G C), s.VirtualEvidence)
    (single : ∀ {n} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (s : OriginalCut G C), s.SingleEndpoint)
    (star : ∀ {n} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (s : OriginalCut G C), s.StarEndpoint)
    (triangle : ∀ {n} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      (s : OriginalCut G C), s.TriangleEndpoint) : DoubleDirtyCase := by
  intro n G inst C four edge least form one witness
  obtain ⟨m,hm,a,ja,b,jb,pins⟩ := witness
  have double := doubleDirty_of_pins one hm ja jb pins
  obtain ⟨H,⟨ht,aff⟩,_⟩ := unique_influenced_top double edge least form
  let s : OriginalCut G C := ⟨m,a,b,H,double,four,edge,least,form,pins,ja,jb,
    (influenced_top_route double edge least form ht aff).1,aff⟩
  exact s.finish (evidence s) (single s) (star s) (triangle s)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
