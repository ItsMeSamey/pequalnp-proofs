import ExactPlaneMatchedBasis
import ExactPlanePhysicalConverse
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace ExactPlaneSmallWitness
open Module Submodule ExactPlanePhysicalConverse
variable {I K B H : Type*} [AddCommGroup K] [Module F K] [Module.Finite F K]
  [AddCommGroup B] [Module F B] [Module.Finite F B]
  [AddCommGroup H] [Module F H] [Module.Finite F H]

/-- A subfamily of the original witness generates the identical physical
    subspace. Its size is bounded by the rank of the keys actually present in
    the witness and the dimension of the gain space. -/
theorem thin (k : I→K) (b : I→B) (h : I→H) (A : Finset I)
    (ok : ExactTrace k b h A) :
    ∃ A' : Finset I, A'⊆A ∧ physicalSpan k b h A'=physicalSpan k b h A ∧
      ExactTrace k b h A' ∧ A'.card ≤
        finrank F (span F (Set.range (fun i : ↥A => k i.val))) + finrank F H := by
  classical
  let S := physicalSpan k b h A
  let W := span F (Set.range (fun i : ↥A => k i.val))
  let col := fun i : I => (k i,b i,h i)
  let q : K × (B × H) →ₗ[F] K := LinearMap.fst F K (B×H)
  have keys : S ≤ W.comap q := by
    apply span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact subset_span ⟨i,rfl⟩
  let key := (q.comp S.subtype).codRestrict W (fun x => keys x.property)
  let gain := ((LinearMap.snd F B H).comp (LinearMap.snd F K (B×H))).comp S.subtype
  let obs := key.prod gain
  have inj : Function.Injective obs := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    have zero : obs x=0 := hx
    have hk : x.val.1=0 := congrArg (fun u : W×H => (u.1:K)) zero
    have hh : x.val.2.2=0 := congrArg Prod.snd zero
    have tagged : (0,x.val.2.1,0) ∈ S := by
      simpa only [←hk,←hh] using x.property
    have hb := (ok x.val.2.1 0).mp tagged
    apply Subtype.ext
    exact Prod.ext hk (Prod.ext hb hh)
  have dim : finrank F S ≤ finrank F W + finrank F H := by
    simpa only [Module.finrank_prod] using LinearMap.finrank_le_finrank_of_injective inj
  let family (i : ↥A) : S := ⟨col i.val,subset_span ⟨i,rfl⟩⟩
  have total : span F (family '' (Finset.univ : Finset ↥A))=⊤ := by
    apply eq_top_iff.mpr
    intro x _
    let R := span F (family '' (Finset.univ : Finset ↥A))
    have le : S ≤ R.map S.subtype := by
      apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨family i,subset_span ⟨i,Finset.mem_univ i,rfl⟩,rfl⟩
    obtain ⟨y,hy,eq⟩ := le x.property
    exact (Subtype.ext eq : y=x) ▸ hy
  obtain ⟨idx,D,_,_,repr_eq⟩ :=
    ExactPlaneMatchedBasis.physical_basis family (Finset.univ : Finset ↥A) total
  let A' := Finset.univ.image (fun j => (idx j).val)
  have sub : A'⊆A := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact (idx j).property
  have same : physicalSpan k b h A'=S := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact subset_span ⟨⟨i.val,sub i.property⟩,rfl⟩
    · let R := physicalSpan k b h A'
      have le : (⊤ : Submodule F S) ≤ R.comap S.subtype := by
        rw [←D.span_eq]
        apply span_le.mpr
        rintro _ ⟨j,rfl⟩
        rw [←repr_eq]
        exact subset_span ⟨⟨(idx j).val,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩,rfl⟩
      intro x hx
      exact le (show (⟨x,hx⟩ : S) ∈ ⊤ from trivial)
  refine ⟨A',sub,same,?_,?_⟩
  · intro z y
    rw [same]
    exact ok z y
  · have c : A'.card ≤ finrank F S := by
      simpa [A'] using (Finset.card_image_le (s:=Finset.univ) (f:=fun j => (idx j).val))
    exact c.trans dim

theorem plane (k : I→K) (b : I→B) (h : I→F×F) (A : Finset I) (ok : ExactTrace k b h A) :
    ∃ A' : Finset I,A'⊆A ∧ ExactTrace k b h A' ∧ A'.card≤
      finrank F (span F (Set.range (fun i : ↥A => k i.val)))+2 := by
  obtain ⟨A',sub,_,hit,bound⟩ := thin k b h A ok
  exact ⟨A',sub,hit,by simpa [Module.finrank_prod] using bound⟩
end ExactPlaneSmallWitness

#print axioms ExactPlaneSmallWitness.thin
#print axioms ExactPlaneSmallWitness.plane
