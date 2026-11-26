import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Finset.Max
namespace ExactPlaneMatchedBasis
open Module Submodule
variable {F I K B H : Type*} [Field F] [Fintype I]
  [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]
  [AddCommGroup H] [Module F H]

theorem extend_matches (k : I→K) (b : I→B) (A : Finset I) (g₀ : K →ₗ[F] B)
    (old : ∀ i∈A,g₀ (k i)=b i) (full : span F (Set.range k)=⊤) :
    ∃ (g : K →ₗ[F] B) (S : Finset I), A⊆S ∧
      (∀ i∈S,g (k i)=b i) ∧ span F (k '' (S : Set I))=⊤ := by
  classical
  let options := (Finset.univ : Finset (Finset I)).filter (fun S => A⊆S ∧
     ∃ f : K →ₗ[F] B, ∀ i∈S, f (k i)=b i)
  have aok : A∈options := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun _ h => h,g₀,old⟩
  obtain ⟨S,hs,big⟩ := options.exists_max_image Finset.card ⟨_,aok⟩
  obtain ⟨asin,g,hg⟩ := (Finset.mem_filter.mp hs).2
  refine ⟨g,S,asin,hg,eq_top_iff.mpr ?_⟩
  rw [←full]
  apply span_le.mpr
  rintro _ ⟨j,rfl⟩
  by_contra fail
  let P := span F (k '' (S : Set I))
  have stay (i) (hi : i∈S) : k i∈P := subset_span ⟨i,hi,rfl⟩
  obtain ⟨f,agree,newtag⟩ := (g.comp P.subtype).exists_extend_of_notMem fail (b j)
  have more : insert j S∈options := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,asin.trans (Finset.subset_insert _ _),f,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|inside
    · exact newtag
    · exact (congrArg (fun q : P →ₗ[F] B => q ⟨k i,stay i inside⟩) agree).trans (hg i inside)
  have bound := big _ more
  have no : j∉S := fun h => fail (stay j h)
  rw [Finset.card_insert_of_notMem no] at bound
  omega
end ExactPlaneMatchedBasis

namespace ExactPlaneMatchedBasis
open Module Submodule
variable {F I K B H : Type*} [Field F] [Fintype I]
  [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]
  [AddCommGroup H] [Module F H]

theorem physical_basis [Module.Finite F K] (k : I→K) (S : Finset I)
    (hs : span F (k '' (S : Set I))=⊤) :
    ∃ (idx : Fin (finrank F K) → I) (D : Basis (Fin (finrank F K)) F K),
      Function.Injective idx ∧ (∀ j,idx j∈S) ∧ ∀ j,k (idx j)=D j := by
  classical
  let h := hs.ge
  let J := (linearIndepOn_empty F id).extend (Set.empty_subset (k '' (S : Set I)))
  let D : Basis J F K := Basis.ofSpan h
  letI : Finite J := Module.Finite.finite_basis D
  letI := Fintype.ofFinite J
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis D).symm
  let D' := D.reindex e
  have rep (j : Fin (finrank F K)) : ∃ i∈S,k i=D' j := by
    apply Basis.ofSpan_subset h
    exact ⟨e.symm j,by rw [show D' j = D (e.symm j) from Basis.reindex_apply D e j]⟩
  choose idx inS matchEq using rep
  exact ⟨idx,D',fun _ _ eq => D'.injective (by simpa only [←matchEq] using congrArg k eq),inS,matchEq⟩

theorem full_chart [Module.Finite F K] (k : I→K) (b : I→B) (A : Finset I)
    (g₀ : K →ₗ[F] B) (old : ∀ i∈A,g₀ (k i)=b i) (full : span F (Set.range k)=⊤) :
    ∃ (g : K →ₗ[F] B) (S : Finset I) (idx : Fin (finrank F K) → I)
      (D : Basis (Fin (finrank F K)) F K),
      A⊆S ∧ (∀ i∈S,g (k i)=b i) ∧ Function.Injective idx ∧
      (∀ j,idx j∈S) ∧ ∀ j,k (idx j)=D j := by
  obtain ⟨g,S,hA,matchS,sp⟩ := extend_matches k b A g₀ old full
  obtain ⟨idx,D,inj,sub,actual⟩ := physical_basis k S sp
  exact ⟨g,S,idx,D,hA,matchS,inj,sub,actual⟩

/-- Physical anchor interpolation and complementary gain columns. The spanning
    premise is the pure-gain trace expressed on the preserved original rows. -/
theorem anchors [Module.Finite F H] {J : Type*} (D : Basis J F K)
    (idx : J→I) (h : I→H) (k : I→K) (S : Finset I)
    (ki : ∀ j,k (idx j)=D j)
    (trace : ∀ L : K →ₗ[F] H, span F ((fun i => h i-L (k i)) '' (S:Set I))=⊤) :
    ∃ (L : K →ₗ[F] H) (extra : Fin (finrank F H) → I)
      (U : Basis (Fin (finrank F H)) F H),
      (∀ j,L (k (idx j))=h (idx j)) ∧ Function.Injective extra ∧
      (∀ i,extra i∈S) ∧ (∀ i,h (extra i)-L (k (extra i))=U i) ∧
      ∀ i j,extra i ≠ idx j := by
  classical
  let L := D.constr F (fun j => h (idx j))
  have agree (j) : L (k (idx j))=h (idx j) := by simp [L,ki,D.constr_basis]
  obtain ⟨extra,U,inj,loc,rep⟩ := physical_basis (fun i => h i-L (k i)) S (trace L)
  refine ⟨L,extra,U,agree,inj,loc,rep,?_⟩
  intro i j eq
  have bad := rep i
  rw [eq,agree,sub_self] at bad
  exact U.ne_zero i bad.symm
end ExactPlaneMatchedBasis

namespace ExactPlaneMatchedBasis
open Module Submodule
variable {F I K H : Type*} [Field F] [AddCommGroup K] [Module F K]
  [AddCommGroup H] [Module F H]

/-- Every physical pure gain remains attainable after subtracting *any*
    linear interpolation on the K pivots, including one chosen later. -/
theorem trace_after_subtract (k : I→K) (h : I→H) (A S : Finset I) (sub : A⊆S)
    (trace : ∀ z : H,(0,z)∈span F ((fun i => (k i,h i)) '' (A:Set I))) :
    ∀ L : K →ₗ[F] H, span F ((fun i => h i-L (k i)) '' (S:Set I))=⊤ := by
  intro L
  let T := span F ((fun i => h i-L (k i)) '' (S:Set I))
  let f : K×H →ₗ[F] H := LinearMap.snd F K H - L.comp (LinearMap.fst F K H)
  have bound : span F ((fun i => (k i,h i)) '' (A:Set I)) ≤ T.comap f := by
    apply span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact subset_span ⟨i,sub hi,rfl⟩
  apply eq_top_iff.mpr
  intro z _
  have hz := bound (trace z)
  change z-L 0∈T at hz
  simpa using hz
end ExactPlaneMatchedBasis

#print axioms ExactPlaneMatchedBasis.full_chart
#print axioms ExactPlaneMatchedBasis.anchors
