import ExactPlaneSuppliedCoordinates

namespace ExactPlaneComputedDeficit
open Module Submodule ExactPlaneResidualPivots ExactPlanePhysicalConverse ExactPlaneObservedSpan
open ExactPlaneFullDirections ExactPlaneSamplerRank ExactPlaneSuppliedCoordinates
variable {N d : ℕ}

/-- Original site IDs whose physical key occurs with every tag in the plane. -/
def complete (p : Fin N → Key d) (b : Fin N → Plane) : Finset (Fin N) :=
  Finset.univ.filter fun i => ∀ t : Plane, ∃ j : Fin N, p j = p i ∧ b j = t

def keyRank (p : Fin N → Key d) (A : Finset (Fin N)) : ℕ :=
  (ExactPlaneEagerBank.basis A p 0 0).card

def computed (p : Fin N → Key d) (b : Fin N → Plane) : ℕ :=
  keyRank p Finset.univ - keyRank p (complete p b)

private def keySpace (p : Fin N → Key d) (A : Finset (Fin N)) :=
  span (ZMod 2) (Set.range fun i : ↥A => p i.val)

theorem keyRank_eq (p : Fin N → Key d) (A : Finset (Fin N)) :
    keyRank p A = finrank (ZMod 2) (span (ZMod 2) (Set.range fun i : ↥A => p i.val)) := by
  let f : Key d →ₗ[ZMod 2] Key d × (Plane × Plane) := LinearMap.inl _ _ _
  have inj : Function.Injective f := fun _ _ eq => congrArg Prod.fst eq
  have image : (keySpace p A).map f = physicalSpan p (0 : Fin N → Plane) (0 : Fin N → Plane) A := by
    unfold keySpace physicalSpan
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨p i.val,⟨i,rfl⟩,rfl⟩
  rw [keyRank,ExactPlaneEagerBank.basis_eq]
  change ExactPlaneGaussianIDs.rank A p 0 0 = _
  rw [ExactPlaneGaussianIDs.rank_eq,←image]
  exact (Submodule.equivMapOfInjective f inj (keySpace p A)).finrank_eq.symm

theorem computed_eq (p : Fin N → Key d) (b : Fin N → Plane) :
    computed p b = deficit (ZMod 2) (key p) b := by
  have univ : Set.range (fun i : ↥(Finset.univ : Finset (Fin N)) => p i.val) = Set.range p := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨⟨i,Finset.mem_univ _⟩,rfl⟩
  let W := observed p
  let D := fullDirections (key p) b
  have eq : W.subtype '' (D : Set W) = Set.range (fun i : ↥(complete p b) => p i.val) := by
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      have all := (mem_fullDirections (key p) b x).mp hx
      obtain ⟨i,hi,_⟩ := all 0
      refine ⟨⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,congrArg Subtype.val hi⟩
      intro t
      obtain ⟨j,hj,hb⟩ := all t
      exact ⟨j,congrArg Subtype.val (hj.trans hi.symm),hb⟩
    · rintro ⟨i,rfl⟩
      refine ⟨key p i.val,(mem_fullDirections (key p) b _).mpr ?_,rfl⟩
      intro t
      obtain ⟨j,hj,hb⟩ := (Finset.mem_filter.mp i.property).2 t
      exact ⟨j,Subtype.ext hj,hb⟩
  have rank := Submodule.finrank_map_subtype_eq W (span (ZMod 2) (D : Set W))
  rw [Submodule.map_span,eq] at rank
  rw [computed,keyRank_eq,keyRank_eq,univ,rank]
  rfl

theorem decision (rows : List (Row d)) (p : Fin N→Key d) (b h : Fin N→Plane)
    (hits : OntoHits rows.toFinset (2*(computed p b+2)+1)) :
    ExactPlaneEagerSelector.runBasis (tables rows p) p b h ≠ none ↔
      ∃ A : Finset (Fin N), ExactTrace p b h A := by
  rw [computed_eq] at hits
  exact supplied_decision rows p b h _ (Nat.le_refl _) hits

#print axioms decision
end ExactPlaneComputedDeficit
