import Q1DoubleAssembly
import DDBranchRealization
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
open Virtual Q0.Factor
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

noncomputable def dag (s : OriginalCut G C) :=
  Virtual.indexed n C (splitCuts n C (orT G C) s.mixer) ((tops G C).erase s.top)
    (opnd C s.mixer) (n+s.top)

theorem forkOfLabel (s : OriginalCut G C) {a t : ℕ} (side : Fin 2)
    (pin : opnd C s.mixer side=n+a) (mem : t∈externalLabels G C s.top a) :
    ∃ f∈s.dag.paidRows, Incidence.Fork s.dag.liveStep (.row f) ∧
      Root.arm side∈s.dag.reaches f ∧ Root.ext t∈s.dag.reaches f := by
  classical
  obtain ⟨et,wrong⟩ := Finset.mem_filter.mp mem
  obtain ⟨ne,ct⟩ := Finset.mem_erase.mp et
  obtain ⟨g,hg⟩ := Finset.not_disjoint_iff_nonempty_inter.mp wrong
  obtain ⟨ja,jt⟩ := Finset.mem_inter.mp hg
  have top := (Finset.mem_filter.mp ct).1
  obtain ⟨H,_,uniq⟩ := unique_influenced_top s.double s.edge s.least s.form
  have eq := uniq s.top ⟨(Finset.mem_filter.mp s.centrelessTop).1,s.influence⟩
  have off : ¬Influence n C s.mixer (n+t) := fun h => ne ((uniq t ⟨top,h⟩).trans eq.symm)
  obtain ⟨f,paid,_,fork,l,r⟩ := Virtual.realized_indexed_label s.double s.edge s.least s.form
    ((tops G C).erase s.top) (Finset.erase_subset _ _) (opnd C s.mixer) (n+s.top) side pin pin
    (Finset.mem_erase.mpr ⟨ne,top⟩) off ja (Finset.mem_of_mem_erase jt)
  exact ⟨f,paid,fork,l,r⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
