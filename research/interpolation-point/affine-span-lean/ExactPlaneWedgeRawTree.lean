import ExactPlaneWedgePublic
import ExactPlaneWedgeDecorate
namespace ExactPlaneWedgeRun
open ExactPlaneWedgeProduct ExactPlaneWedgeCodec ExactPlaneWedgeTree ExactPlaneWedgeDecorate
open ExactPlaneWedgeDecision ExactPlaneResidualPivots
open ExactPlanePhysicalConverse (ExactTrace)
variable {d n : Nat}
def raw (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane) : Option (Sites n × Sites n) :=
  solve (decorate k t ∅) k b h

theorem raw_spec (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane)
    (sep : separated t) (cover : leaves t=Finset.univ) :
    (∀ uv,raw t k b h=some uv → Good k b h uv.1 uv.2 ∧ ExactTrace k b h (uv.1∪uv.2)) ∧
    (raw t k b h≠none ↔ ∃ A,ExactTrace k b h A) :=
  physical (decorate k t ∅) k b h (by simpa only [tree_decorate] using sep)
    (by simpa only [tree_decorate] using cover) (by simpa [subspace] using decorate_valid k t ∅)
theorem empty_no (k : Fin 0→Word d) (b h : Fin 0→Plane) :
    ¬∃ A,ExactTrace k b h A := by
  rintro ⟨A,ok⟩
  obtain ⟨_,u,v,_,_,_,_,_,ind⟩ := (ExactPlaneRelationPair.exact_pair k b h A).mp ok
  have z (w : Fin 0→ZMod 2) : w=0 := funext fun i=>Fin.elim0 i
  have nz := (ExactPlaneResidualPivots.det_ne_iff _ _).mpr ind
  rw [z u,z v,map_zero] at nz
  exact nz (by rfl)
#print axioms raw_spec
end ExactPlaneWedgeRun
