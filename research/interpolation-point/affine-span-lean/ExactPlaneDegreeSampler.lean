import ExactPlaneDegreeSpan
import ExactPlaneConstructedRows
import ExactPlaneOddChartList
import ExactPlaneSamplerRank

namespace ExactPlaneDegreeSampler
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit
open ExactPlaneSamplerSpan ExactPlaneSamplerRank ExactPlaneOddChartList
open ExactPlaneConstructedRows ExactPlaneNumericalRows
open Classical

def ordered {C : Type*} (seed : List C) (D : ℕ) : List (List C) :=
  (List.range (D/2+1)).flatMap (fun j => ExactPlaneOddChartList.words seed (2*j+1))

theorem mem_ordered {C : Type*} (seed : List C) (D : ℕ) (l : List C) :
    l ∈ ordered seed D ↔ (∀ x ∈ l,x ∈ seed) ∧ l.length%2=1 ∧ l.length≤2*(D/2)+1 := by
  simp only [ordered,List.mem_flatMap,List.mem_range,ExactPlaneOddChartList.mem_words]
  constructor
  · rintro ⟨j,hj,len,inside⟩
    exact ⟨inside,by omega,by omega⟩
  · rintro ⟨inside,odd,cap⟩
    exact ⟨l.length/2,by omega,by omega,inside⟩

theorem ordered_count {C : Type*} (seed : List C) (D : ℕ) :
    (ordered seed D).length =
      ((List.range (D/2+1)).map (fun j => seed.length^(2*j+1))).sum := by
  simp [ordered,List.length_flatMap,Function.comp_def,ExactPlaneOddChartList.length_words]

def candidates (m r D : ℕ) : List (Vec (Fin m)) :=
  (ordered (points (generate m (r+1))) D).map List.sum

theorem generated_hit (m r D : ℕ) (A : AffineSubspace F (Vec (Fin m)))
    (rank : Module.finrank F ((Vec (Fin m)) ⧸ A.direction) ≤ r)
    (c : Coeff (Fin m)) (degree : degreeLE D c)
    (hit : ∃ x ∈ A,eval c (support x) ≠ 0) :
    ∃ l ∈ ordered (points (generate m (r+1))) D,
      (∀ x∈l,x∈A) ∧ l.sum∈A ∧ eval c (support l.sum) ≠ 0 := by
  classical
  obtain ⟨x,hx,nz⟩ := hit
  let seed := (points (generate m (r+1))).toFinset
  let T := seed.filter fun x => x∈A
  have eq : affineSpan F (T : Set (Vec (Fin m)))=A :=
    span_coset seed r (hits_of_onto (generate_hits m (r+1))) A x hx rank
  obtain ⟨l,inside,odd,cap,member,nonzero⟩ := degree_span_hit D T c degree ⟨x,eq.symm ▸ hx,nz⟩
  refine ⟨l,(mem_ordered _ _ _).mpr ⟨?_,odd,cap⟩,?_,eq ▸ member,nonzero⟩
  · intro p hp
    exact List.mem_toFinset.mp (Finset.mem_filter.mp (inside p hp)).1
  · intro p hp
    exact (Finset.mem_filter.mp (inside p hp)).2

theorem generated_hit_rows (m r D : ℕ) (read : Vec (Fin m) →ₗ[F] Vec (Fin r))
    (x₀ : Vec (Fin m)) (c : Coeff (Fin m)) (degree : degreeLE D c)
    (hit : ∃ x,read x = read x₀ ∧ eval c (support x) ≠ 0) :
    ∃ l ∈ ordered (points (generate m (r+1))) D,
      (∀ x∈l,read x=read x₀) ∧ read l.sum=read x₀ ∧ eval c (support l.sum) ≠ 0 := by
  let A := AffineSubspace.mk' x₀ (LinearMap.ker read)
  have mem (x : Vec (Fin m)) : x∈A ↔ read x = read x₀ := by
    change x∈AffineSubspace.mk' x₀ (LinearMap.ker read) ↔ _
    rw [AffineSubspace.mem_mk']
    change read (x-x₀)=0 ↔ _
    rw [map_sub,sub_eq_zero]
  have rank : Module.finrank F ((Vec (Fin m)) ⧸ A.direction) ≤ r := by
    rw [show A.direction=LinearMap.ker read by exact AffineSubspace.direction_mk' _ _,
      read.quotKerEquivRange.finrank_eq]
    exact (LinearMap.range read).finrank_le.trans_eq (Module.finrank_fin_fun F)
  obtain ⟨x,hx,nz⟩ := hit
  obtain ⟨l,hl,inside,ok,pos⟩ := generated_hit m r D A rank c degree ⟨x,(mem x).mpr hx,nz⟩
  exact ⟨l,hl,fun p hp => (mem p).mp (inside p hp),(mem _).mp ok,pos⟩

def search (m r D : ℕ) (test : Vec (Fin m) → Bool) : Option (Vec (Fin m)) :=
  (candidates m r D).find? test

theorem search_complete (m r D : ℕ) (A : AffineSubspace F (Vec (Fin m)))
    (rank : Module.finrank F ((Vec (Fin m)) ⧸ A.direction) ≤ r)
    (c : Coeff (Fin m)) (degree : degreeLE D c)
    (test : Vec (Fin m) → Bool) (spec : ∀ x,test x=true ↔ x∈A ∧ eval c (support x)≠0) :
    (search m r D test).isSome=true ↔ ∃ x∈A,eval c (support x)≠0 := by
  constructor
  · intro yes
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp yes
    exact ⟨x,(spec x).mp (List.find?_some hx)⟩
  · intro hit
    obtain ⟨l,hl,_,inside,nz⟩ := generated_hit m r D A rank c degree hit
    have mem : l.sum∈candidates m r D := List.mem_map.mpr ⟨l,hl,rfl⟩
    cases h : search m r D test with
    | some _ => rfl
    | none =>
      have no := (List.find?_eq_none.mp h) l.sum mem
      exact False.elim (no ((spec _).mpr ⟨inside,nz⟩))

#print axioms generated_hit
#print axioms search_complete
end ExactPlaneDegreeSampler
