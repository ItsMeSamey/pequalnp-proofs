import ExactPlaneSmallWitness
import ExactPlaneObservedSpan
import ExactPlaneGlobalApplication

namespace ExactPlaneAcceptedSmallWitness
open Module Submodule ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlaneObservedSpan ExactPlaneGlobalApplication
variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K] {N : Nat}

theorem physical (k : Fin N→K) (tag h : Fin N→Plane) (A : Finset (Fin N))
    (hit : ExactTrace k tag h A) :
    ∃ S : Finset (Fin N), S⊆A ∧ physicalSpan k tag h S=physicalSpan k tag h A ∧
      ExactTrace k tag h S ∧ S.card≤finrank (ZMod 2) (observed k)+2 := by
  classical
  letI := ExactPlaneObservedSpan.finite k
  obtain ⟨S,sub,eq,ok,bd⟩ := ExactPlaneSmallWitness.thin (key k) tag h A
    ((trace_iff k tag h A).mpr hit)
  refine ⟨S,sub,?_,(trace_iff k tag h S).mp ok,?_⟩
  · rw [←map_physical k tag h S,←map_physical k tag h A,eq]
  · have le := Submodule.finrank_le
      (span (ZMod 2) (Set.range (fun i : ↥A => key k i.val)))
    have dim : finrank (ZMod 2) Plane=2 := by simp [Plane,Module.finrank_prod]
    rw [dim] at bd
    exact bd.trans (Nat.add_le_add_right le 2)

theorem recovered (k : Fin N→K) (tag h : Fin N→Plane) (g : K→ₗ[ZMod 2] Plane)
    (hit : Recovered k tag h g) :
    ∃ S : Finset (Fin N), S⊆accepted k tag g ∧
      (∀ i∈S, tag i=g (k i)) ∧ physicalSpan k tag h S=physicalSpan k tag h (accepted k tag g) ∧
      ExactTrace k tag h S ∧ S.card≤finrank (ZMod 2) (observed k)+2 := by
  obtain ⟨S,sub,eq,ok,bd⟩ := physical k tag h (accepted k tag g) hit.1
  exact ⟨S,sub,fun i hi => (Finset.mem_filter.mp (sub hi)).2,eq,ok,bd⟩

#print axioms physical
#print axioms recovered
end ExactPlaneAcceptedSmallWitness
