import ExactPlanePairSearch
namespace ExactPlanePairSearch
open ExactPlaneFirstRelation ExactPlanePhysicalConverse ExactPlaneResidualPivots
variable {r d N : Nat}

theorem concrete_basis (k : Fin N→Key d) (b h : Fin N→Plane) (B : Module.Basis (Fin r) F (first k b)) :
    let row := fun j=>(B j).val
    (pairs row).length=4^r ∧ (solve row k b h≠none ↔ ∃ A : Finset (Fin N), ExactTrace k b h A) ∧
      ∀ A,solve row k b h=some A→ExactTrace k b h A :=
  ⟨count _,complete _ k b h (basis_covers k b B),fun _ ok=>returned ok⟩

/-- Oracle-free mathematical existence chooses a basis of the intrinsic first
relation space. The executable scan accepts its rows explicitly. -/
theorem finite_pair_bound (k : Fin N→Key d) (b h : Fin N→Plane) :
    let r := Module.finrank F (first k b)
    ∃ row : Fin r→Fin N→F, (pairs row).length=4^r ∧
      (solve row k b h≠none ↔ ∃ A : Finset (Fin N), ExactTrace k b h A) ∧
      ∀ A,solve row k b h=some A→ExactTrace k b h A := by
  let B := Module.finBasis F (first k b)
  exact ⟨_,concrete_basis k b h B⟩
#print axioms finite_pair_bound
end ExactPlanePairSearch
