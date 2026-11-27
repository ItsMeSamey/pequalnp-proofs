import ExactPlaneProfileSlice
namespace ExactPlanePeriodSlice
open ExactPlaneProfileCharts ExactPlaneSuppliedCoordinates
open ExactPlaneSamplerRank ExactPlaneConstructedRows ExactPlaneNumericalRows
abbrev F := ZMod 2
variable {d t N m k : Nat}
abbrev Space (m : Nat) := Fin m → F

noncomputable def quotientRead (W : Submodule F (Space m)) :
    Space m →ₗ[F] Space (Module.finrank F ((Space m) ⧸ W)) :=
  (Module.finBasis F ((Space m) ⧸ W)).equivFun.toLinearMap.comp W.mkQ

theorem quotientRead_eq (W : Submodule F (Space m)) (x y : Space m) :
    quotientRead W x = quotientRead W y ↔ x-y∈W := by
  change (Module.finBasis F ((Space m) ⧸ W)).equivFun (W.mkQ x) =
    (Module.finBasis F ((Space m) ⧸ W)).equivFun (W.mkQ y) ↔ _
  rw [EmbeddingLike.apply_eq_iff_eq]
  exact Submodule.Quotient.eq W

theorem single (W : Submodule F (Space m)) (read : Space m →ₗ[F] Space k) (x₀ : Space m) :
    ∃ x∈points (generate m (Module.finrank F ((Space m) ⧸ W)+k)), x-x₀∈W ∧ read x=read x₀ := by
  let q := Module.finrank F ((Space m) ⧸ W)
  let rows : Fin (q+k) → Space m →ₗ[F] F := Fin.addCases
    (fun i => (LinearMap.proj i).comp (quotientRead W))
    (fun i => (LinearMap.proj i).comp read)
  obtain ⟨x,mem,agree⟩ := hits_of_onto (generate_hits m (q+k)) (q+k) le_rfl rows x₀
  refine ⟨x,List.mem_toFinset.mp mem,(quotientRead_eq W x x₀).mp ?_,?_⟩
  · funext i
    simpa [rows] using agree (Fin.castAdd k i)
  · funext i
    simpa [rows] using agree (Fin.natAdd q i)

theorem period_sites (W : Submodule F (X d)) (priv : Fin N→Key d) (site : Fin (t+2)→Fin N)
    (x₀ : X d) :
    ∃ x∈points (generate (d+d) (Module.finrank F ((X d) ⧸ W)+2*(t+2))),
      x-x₀∈W ∧ ∀j,table priv x (site j)=table priv x₀ (site j) := by
  obtain ⟨x,hx,per,eq⟩ := single W (measurements priv site) x₀
  exact ⟨x,hx,per,(measurements_eq _ _ _ _).mp eq⟩

#print axioms period_sites
end ExactPlanePeriodSlice
