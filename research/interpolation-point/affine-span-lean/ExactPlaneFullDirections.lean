import ExactPlanePrescribedBasis
namespace ExactPlaneFullDirections
open Module Submodule Classical
variable {I K B : Type*} [Fintype I]

/-- Every tag must have a physical representative at this very key. -/
def Full (k : I→K) (b : I→B) (x : K) := ∀ t : B,∃ i,k i=x ∧ b i=t

noncomputable def fullDirections (k : I→K) (b : I→B) : Finset K :=
  (Finset.univ.image k).filter (Full k b)

theorem mem_fullDirections [Nonempty B] (k : I→K) (b : I→B) (x : K) :
    x∈fullDirections k b ↔ Full k b x := by
  classical
  refine ⟨fun h => (Finset.mem_filter.mp h).2,fun h => ?_⟩
  obtain ⟨i,eq,_⟩ := h (Classical.choice (inferInstance : Nonempty B))
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq⟩,h⟩

variable (F : Type*) [Field F] [AddCommGroup K] [Module F K]
theorem select (k : I→K) (b : I→B) :
    ∃ D₀ : Finset K,D₀⊆fullDirections k b ∧ LinearIndepOn F id (D₀ : Set K) ∧
       span F (D₀ : Set K)=span F (fullDirections k b : Set K) := by
  classical
  let S := fullDirections k b
  let empty := linearIndepOn_empty F (id : K→K)
  let inc := Set.empty_subset (S : Set K)
  let T := empty.extend inc
  have sub : T⊆(S:Set K) := empty.extend_subset inc
  have finite : T.Finite := S.finite_toSet.subset sub
  refine ⟨finite.toFinset,?_,?_,?_⟩
  · intro x hx; exact sub (finite.mem_toFinset.mp hx)
  · simpa only [Set.Finite.coe_toFinset] using empty.linearIndepOn_extend inc
  · simpa only [Set.Finite.coe_toFinset] using empty.span_extend_eq_span inc

variable [Module.Finite F K] [AddCommGroup B] [Module F B]
noncomputable def deficit (k : I→K) (b : I→B) :=
  finrank F K-finrank F (span F (fullDirections k b : Set K))

theorem maximal_branch (k : I→K) (b : I→B) (A : Finset I)
    (g₀ : K →ₗ[F] B) (old : ∀ i∈A,g₀ (k i)=b i) (full : span F (Set.range k)=⊤) :
    ∃ (g : K →ₗ[F] B) (T : Finset K) (D : Basis T F K) (idx : T→I),
      (∀ i∈A,g (k i)=b i) ∧ (∀ j,D j=j.val) ∧
      (∀ j,k (idx j)=D j ∧ b (idx j)=g (D j)) ∧
      (T.filter (fun x => ¬Full k b x)).card=deficit F k b := by
  classical
  obtain ⟨D₀,sub,ind,same⟩ := select F k b
  have tags (x) (hx : x∈D₀) := (mem_fullDirections k b x).mp (sub hx)
  obtain ⟨g,T,D,idx,pres,ins,basis,rep,cnt⟩ :=
    ExactPlaneMatchedBasis.prescribed_basis k b A g₀ old full D₀ ind tags
  have cover (x) (hf : Full k b x) : x∈span F (D₀:Set K) := by
    rw [same]; exact subset_span ((mem_fullDirections k b x).mpr hf)
  have eq : T.filter (fun x => ¬Full k b x)=T \ D₀ := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · rintro ⟨hx,no⟩
      exact ⟨hx,fun m => no (tags x m)⟩
    · rintro ⟨hx,no⟩
      exact ⟨hx,ExactPlaneMatchedBasis.outside_not_full D₀ T D ins basis (Full k b) cover ⟨x,hx⟩ no⟩
  exact ⟨g,T,D,idx,pres,basis,rep,by rw [eq]; unfold deficit; rw [←same]; exact cnt⟩

#print axioms maximal_branch
end ExactPlaneFullDirections
