import ExactPlaneSuccessTrace
namespace ExactPlaneSectionGraph
open ExactPlanePhysicalResidual ExactPlaneResidualPivots
open ExactPlanePhysicalConverse (ExactTrace physicalSpan)
open scoped BigOperators
variable {I J K B H : Type*} [AddCommGroup K] [Module F K]
  [AddCommGroup B] [Module F B] [AddCommGroup H] [Module F H]

private theorem self_add {V : Type*} [AddCommGroup V] [Module F V] (v : V) : v+v=0 := by
  have z : (1:F)+1=0 := by decide
  calc
    v+v = ((1:F)+1) • v := by simp [add_smul]
    _ = 0 := by rw [z,zero_smul]

private def graphMap (g : K →ₗ[F] B) (L : K →ₗ[F] H) : K →ₗ[F] K × B × H :=
  LinearMap.id.prod (g.prod L)

private def vertical : H →ₗ[F] K × B × H :=
  (0 : H →ₗ[F] K).prod ((0 : H →ₗ[F] B).prod LinearMap.id)

private def strip (L : K →ₗ[F] H) : (K × B × H) →ₗ[F] H :=
  (LinearMap.snd F B H).comp (LinearMap.snd F K (B × H)) + L.comp (LinearMap.fst F K (B × H))

private def mismatch (g : K →ₗ[F] B) : (K × B × H) →ₗ[F] B :=
  (LinearMap.fst F B H).comp (LinearMap.snd F K (B × H)) - g.comp (LinearMap.fst F K (B × H))

theorem span_iff [Fintype J] (A : Finset I) (k : I → K) (b : I → B) (h : I → H)
    (g : K →ₗ[F] B) (L : K →ₗ[F] H)
    (matched : ∀ i∈A, b i=g (k i))
    (e : Module.Basis J F K)
    (sections : ∀ j, (e j,g (e j),L (e j)) ∈ indexedSpan A (col k b h))
    (x : K) (y : B) (z : H) :
    (x,y,z) ∈ indexedSpan A (col k b h) ↔
      y=g x ∧ z + L x ∈ indexedSpan A (residual k h L) := by
  classical
  let S := indexedSpan A (col k b h)
  let T := indexedSpan A (residual k h L)
  have phys (i : I) (hi : i∈A) : col k b h i ∈ S :=
    Submodule.subset_span ⟨i,hi,rfl⟩
  have graph (u : K) : graphMap g L u ∈ S := by
    rw [← e.sum_repr u]
    rw [map_sum]
    apply S.sum_mem
    intro j _
    rw [map_smul]
    apply S.smul_mem
    exact sections j
  have liftT : T ≤ S.comap (vertical (K:=K) (B:=B)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change (0,0,residual k h L i) ∈ S
    have add := S.add_mem (phys i hi) (graph (k i))
    change (k i+k i,b i+g (k i),h i+L (k i)) ∈ S at add
    simpa [residual,matched i hi,self_add] using add
  constructor
  · intro hx
    have keep : S ≤ T.comap (strip L) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,hi,rfl⟩
      exact Submodule.subset_span ⟨i,hi,rfl⟩
    have agree : S ≤ LinearMap.ker (mismatch g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,hi,rfl⟩
      change b i - g (k i)=0
      exact sub_eq_zero.mpr (matched i hi)
    exact ⟨sub_eq_zero.mp (show y - g x=0 from agree hx),keep hx⟩
  · rintro ⟨rfl, hz⟩
    have add := S.add_mem (graph x) (liftT hz)
    change (x+0,g x+0,L x+(z+L x)) ∈ S at add
    have reduce : L x+(z+L x)=z := calc
      _ = z+(L x+L x) := by ac_rfl
      _ = z := by rw [self_add,add_zero]
    simpa only [add_zero,reduce] using add

theorem supported (A U : Finset I) (k : I→K) (b : I→B) (h : I→H)
    (g : K→ₗ[F] B) (sub : U ⊆ A) (matchTag : ∀ i∈A,b i=g (k i)) :
    (∑ i∈U,k i,g (∑ i∈U,k i),∑ i∈U,h i) ∈ indexedSpan A (col k b h) := by
  classical
  apply (physical_support A _ _).mpr
  refine ⟨U,sub,?_⟩
  ext <;> simp [col,Prod.fst_sum,Prod.snd_sum,Finset.sum_congr rfl (fun i hi => matchTag i (sub hi))]

private theorem asPhysical (A : Finset I) (k : I→K) (b : I→B) (h : I→H) :
    indexedSpan A (col k b h) = physicalSpan k b h A := by
  unfold indexedSpan physicalSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩

theorem exact_iff_pivots [Fintype J] (A : Finset I) (k : I→K) (b h : I→Plane)
    (g L : K→ₗ[F] Plane) (matchTag : ∀ i∈A,b i=g (k i)) (e : Module.Basis J F K)
    (sections : ∀ j, (e j,g (e j),L (e j)) ∈ indexedSpan A (col k b h)) :
    ExactTrace k b h A ↔ ∃ i∈A, ∃ j∈A, Independent (residual k h L i) (residual k h L j) := by
  classical
  have eq (z v : Plane) : (0,z,v) ∈ physicalSpan k b h A ↔
      z=0 ∧ v∈indexedSpan A (residual k h L) := by
    rw [←asPhysical]
    simpa using span_iff A k b h g L matchTag e sections 0 z v
  constructor
  · intro trace
    have all (v : Plane) := ((eq 0 v).mp ((trace 0 v).mpr rfl)).2
    exact pivots A _ (all (1,0)) (all (0,1)) ((det_ne_iff _ _).mp (by decide))
  · rintro ⟨i,hi,j,hj,ind⟩
    let v := fun t : Fin 2 => if t=0 then residual k h L i else residual k h L j
    have whole := ind.span_eq_top_of_card_eq_finrank
      (by simp [Plane,Module.finrank_prod] : Fintype.card (Fin 2)=Module.finrank F Plane)
    have le : Submodule.span F (Set.range v) ≤ indexedSpan A (residual k h L) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t,rfl⟩
      by_cases ht : t=0
      · simp only [v,if_pos ht]
        exact Submodule.subset_span ⟨i,hi,rfl⟩
      · simp only [v,if_neg ht]
        exact Submodule.subset_span ⟨j,hj,rfl⟩
    change Submodule.span F (Set.range v)=⊤ at whole
    rw [whole] at le
    intro z y
    rw [eq]
    exact and_iff_left (le (Submodule.mem_top))

/-- Left basis directions use sums of accepted sites. Right directions use
single accepted complement sites. The same support can occur several times. -/
theorem mixed_pivots {P Q : Type*} [Fintype P] [Fintype Q] (A : Finset I)
    (k : I→K) (b h : I→Plane) (g L : K→ₗ[F] Plane)
    (matchTag : ∀ i∈A,b i=g (k i)) (e : Module.Basis (P ⊕ Q) F K)
    (U : P→Finset I) (idx : Q→I)
    (inside : ∀ p,U p ⊆ A) (sk : ∀ p, ∑ i∈U p,k i=e (Sum.inl p))
    (sh : ∀ p, ∑ i∈U p,h i=L (e (Sum.inl p)))
    (anchor : ∀ q,idx q∈A) (ak : ∀ q,k (idx q)=e (Sum.inr q))
    (ah : ∀ q,h (idx q)=L (e (Sum.inr q))) :
    ExactTrace k b h A ↔ ∃ i∈A, ∃ j∈A, Independent (residual k h L i) (residual k h L j) := by
  apply exact_iff_pivots A k b h g L matchTag e
  intro t
  cases t with
  | inl p => simpa only [sk p,sh p] using supported A (U p) k b h g (inside p) matchTag
  | inr q =>
    have mem : col k b h (idx q) ∈ indexedSpan A (col k b h) :=
      Submodule.subset_span ⟨idx q,anchor q,rfl⟩
    simpa only [col,matchTag _ (anchor q),ak q,ah q] using mem

#print axioms exact_iff_pivots
end ExactPlaneSectionGraph
