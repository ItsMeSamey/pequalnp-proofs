import ExactPlaneProfileCharts
import ExactPlaneDegreeSampler
namespace ExactPlaneProfileCharts
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
open ExactPlaneAffineSubstitution (Coeff)
open ExactPlaneAffineSpanHit (support)
open ExactPlaneSubsetPolynomial (degreeLE eval)
open ExactPlaneDegreeSampler (ordered)
variable {N d t D : ℕ}

private noncomputable def slots (t : Nat) : (Fin (t+2) × Bool) ≃ Fin (2*(t+2)) :=
  Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])

private def bit : Bool → Plane →ₗ[ZMod 2] ZMod 2
  | false => LinearMap.fst _ _ _
  | true => LinearMap.snd _ _ _

noncomputable def measurements (priv : Fin N→Key d) (site : Fin (t+2)→Fin N) :
    X d →ₗ[ZMod 2] (Fin (2*(t+2))→ZMod 2) :=
  LinearMap.pi fun j=>(bit ((slots t).symm j).2).comp (read (priv (site ((slots t).symm j).1)))

theorem measurements_eq (priv : Fin N→Key d) (site : Fin (t+2)→Fin N) (x y : X d) :
    measurements priv site x=measurements priv site y ↔
      ∀ j,table priv x (site j)=table priv y (site j) := by
  classical
  have atbit (u : X d) (i : Fin (t+2)) (b : Bool) :
      measurements priv site u (slots t (i,b)) = bit b (table priv u (site i)) := by
    simp only [measurements,LinearMap.pi_apply,LinearMap.comp_apply,Equiv.symm_apply_apply,table_chart]
    rfl
  constructor
  · intro h j
    exact Prod.ext (by simpa only [atbit,bit,LinearMap.fst_apply,LinearMap.snd_apply] using congrFun h (slots t (j,false)))
      (by simpa only [atbit,bit,LinearMap.fst_apply,LinearMap.snd_apply] using congrFun h (slots t (j,true)))
  · intro h
    funext i
    obtain ⟨⟨j,b⟩,rfl⟩ := (slots t).surjective i
    rw [atbit,atbit,h]

theorem sample_slice (priv : Fin N→Key d) (site : Fin (t+2)→Fin N)
    (x₀ : X d) (c : Coeff (Fin (d+d))) (deg : degreeLE D c) (hit : eval c (support x₀)≠0) :
    ∃ l∈ordered (ExactPlaneNumericalRows.points (ExactPlaneConstructedRows.generate (d+d) (2*(t+2)+1))) D,
      (∀ j, table priv l.sum (site j)=table priv x₀ (site j)) ∧ eval c (support l.sum)≠0 := by
  obtain ⟨l,hl,_,same,nonzero⟩ := ExactPlaneDegreeSampler.generated_hit_rows
    (d+d) (2*(t+2)) D (measurements priv site) x₀ c deg ⟨x₀,rfl,hit⟩
  exact ⟨l,hl,(measurements_eq priv site _ _).mp same,nonzero⟩
end ExactPlaneProfileCharts
