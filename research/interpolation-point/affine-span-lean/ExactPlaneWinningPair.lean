import ExactPlaneFirstRankBasis
namespace ExactPlanePairSearch
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneFirstRelation ExactPlaneFirstRank
variable {r N d : Nat}
theorem compatible_winner {row : Fin r→Fin N→F} {k : Fin N→Key d} {b h : Fin N→Plane}
    (good : ∀x,combine row x∈first k b) {w : WordPair N} (ok : findPair row k b h=some w) :
    ∃ g : Key d→ₗ[F] Plane,w.1∈relation k b g ∧ w.2∈relation k b g ∧
      Independent (aggregate h w.1) (aggregate h w.2) ∧ ExactTrace k b h (indices w) := by
  obtain ⟨ind,tr⟩ := (test_iff k b h w).mp (List.find?_some ok)
  obtain ⟨g,mt⟩ := ExactPlanePhysicalConverse.chart k b h (indices w) tr
  have mem := List.mem_of_find?_eq_some ok
  obtain ⟨u,hu,hm⟩ := List.mem_flatMap.mp mem
  obtain ⟨x,_,ex⟩ := List.mem_map.mp hu
  obtain ⟨v,hv,ew⟩ := List.mem_map.mp hm
  obtain ⟨y,_,ey⟩ := List.mem_map.mp hv
  subst w
  refine ⟨g,(mem_relation _ _ _ _).mpr ⟨?_,fun i hi=>mt i (Finset.mem_union_left _ hi)⟩,
    (mem_relation _ _ _ _).mpr ⟨?_,fun i hi=>mt i (Finset.mem_union_right _ hi)⟩,ind,tr⟩
  · exact private_zero k b (ex ▸ good x)
  · exact private_zero k b (ey ▸ good y)
#print axioms compatible_winner
end ExactPlanePairSearch
