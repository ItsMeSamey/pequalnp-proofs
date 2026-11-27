import ExactPlaneGaussianCandidate
namespace ExactPlaneGaussianCandidate
open ExactPlaneGaussianPacking ExactPlaneFiveQueries ExactPlanePhysicalConverse
open scoped BigOperators
variable {d : ℕ} {I : Type*} [DecidableEq I] [Fintype I]

theorem supportQuery_sound (A : List I) (k : I → Key d) (b h : I → P)
    (y : V (Key d)) (U : Finset I) (ok : supportQuery A k b h y=some U) :
    U⊆A.toFinset ∧ ExactPlaneCandidateCheck.total k b h U=y := by
  classical
  cases hm : query A k b h y with
  | none => simp [supportQuery,hm] at ok
  | some mask =>
    have eq : A.toFinset.filter (fun i => mask i=1)=U := by simpa [supportQuery,hm] using ok
    subst U
    refine ⟨Finset.filter_subset _ _,pack_injective ?_⟩
    obtain ⟨value,outside⟩ := ExactPlaneGaussian.solve_witness A _ _ mask hm
    let col := fun i => pack (k i,b i,h i)
    have decode : (∑ i,mask i • col i)=pack y := by
      simpa [ExactPlaneGaussian.decode,LinearMap.sum_apply,col] using value
    rw [ExactPlaneCandidateCheck.total,map_sum,Finset.sum_filter,←decode]
    calc
      _ = ∑ i ∈ A.toFinset,mask i • col i := by
        apply Finset.sum_congr rfl
        intro i _
        have bit : ∀ a : F,a=0 ∨ a=1 := by decide
        rcases bit (mask i) with h|h <;> simp [h,col]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
        intro i _ hi
        have zero := outside i (by simpa using hi)
        simp [zero])

theorem supports_spec (A : List I) (k : I → Key d) (b h : I → P) :
    ((supports A k b h).isSome=true ↔ ExactTrace k b h A.toFinset) ∧
    ∀ u v,supports A k b h=some (u,v) →
      (u⊆A.toFinset ∧ ExactPlaneCandidateCheck.total k b h u=(0,0,one)) ∧
      (v⊆A.toFinset ∧ ExactPlaneCandidateCheck.total k b h v=(0,0,two)) := by
  refine findSupports_spec A.toFinset k b h (supportQuery A k b h) ?_ ?_
  · intro y
    simpa [supportQuery] using query_iff A k b h y
  · exact supportQuery_sound A k b h

#print axioms supports_spec
end ExactPlaneGaussianCandidate
