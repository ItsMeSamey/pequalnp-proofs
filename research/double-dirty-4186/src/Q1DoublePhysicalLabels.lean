import DDRootRegion
import Q1DoubleShapes
import DDVirtualDAG
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable def externalLabels (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (H a : ℕ) : Finset ℕ := by
  classical
  exact ((centreless G C).erase H).filter fun t =>
    ¬Disjoint (andRegion n C a) ((andRegion n C t).erase t)

theorem noLeakOfEmpty {H a b : ℕ}
    (left : externalLabels G C H a=∅) (right : externalLabels G C H b=∅)
    (t : ℕ) (ht : t∈centreless G C) (ne : t≠H) :
    Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C t).erase t) := by
  classical
  have each (r : ℕ) (empty : externalLabels G C H r=∅) :
      Disjoint (andRegion n C r) ((andRegion n C t).erase t) := by
    by_contra wrong
    have mem : t∈externalLabels G C H r := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne,ht⟩,wrong⟩
    simp [empty] at mem
  exact Finset.disjoint_left.mpr fun g hg h =>
    (Finset.mem_union.mp hg).elim (fun x => Finset.disjoint_left.mp (each a left) x h)
      (fun x => Finset.disjoint_left.mp (each b right) x h)

def Represents (V : Virtual.DAG) (labels : Finset ℕ) (side : Fin 2) : Prop :=
  ∀ t∈labels, ∃ g∈V.paidRows, V.reaches g = {Virtual.Root.arm side, Virtual.Root.ext t}

theorem classifyPhysical {H a b : ℕ} (V : Virtual.DAG)
    (left : Represents V (externalLabels G C H a) 0)
    (right : Represents V (externalLabels G C H b) 1)
    (meet : ∀ i∈V.paidRows, ∀ j∈V.paidRows, i≠j →
      (V.reaches i).card=2 → (V.reaches j).card=2 →
      ((V.reaches i) ∩ (V.reaches j)).Nonempty) :
    LeakShape (externalLabels G C H a) (externalLabels G C H b) := by
  classical
  apply classifyLeaks
  intro p hp q hq
  obtain ⟨i,hi,rootsI⟩ := left p hp
  obtain ⟨j,hj,rootsJ⟩ := right q hq
  have ne : i≠j := by
    rintro rfl
    have k : Virtual.Root.arm 0∈V.reaches i := by simp [rootsI]
    simp [rootsJ] at k
  obtain ⟨r,hr⟩ := meet i hi j hj ne (by simp [rootsI]) (by simp [rootsJ])
  obtain ⟨pi,qj⟩ := Finset.mem_inter.mp hr
  rw [rootsI] at pi
  rw [rootsJ] at qj
  cases r <;> simp_all


end PEqualNP.Outside.L_meta_4186_aux.Q1Double
