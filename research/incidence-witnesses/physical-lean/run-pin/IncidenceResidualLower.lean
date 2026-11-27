import IncidenceResidualPath
import IncidenceResidualEndLedger
import IncidenceResidualDemand
namespace IncidenceResidualLower
open CircuitRewire IncidenceResidualCut IncidenceResidualPath IncidenceResidualPorts
open IncidenceResidualDemand
open scoped BigOperators

theorem lower {m k : ℕ} (C : Model m) (G : Graph C k) (hk : 1<k)
    (live : ∀ i<m+C.s,0<readers C.g C.s C.out i) :
    2*m-1-(2*m)/(k+1)≤C.s := by
  classical
  choose e cert using endpoint C G live
  let single := fun x : Fin m => ({x}:Mask m)
  let A := accepted m single C.X
  let W := fun i=> min k (A i).card
  have inj : Function.Injective e := by
    intro x y eq
    have hot := ((cert x).2.1 x).2 rfl
    rw [eq] at hot
    exact ((cert y).2.1 x).1 hot
  let T := Finset.univ.image e
  let B := T.filter fun i=>2≤readers C.g C.s C.out i
  let S := T \ B
  have subset : B⊆T := Finset.filter_subset _ _
  have population : T.card=m := by simp [T,Finset.card_image_of_injective _ inj]
  have thin (i : ℕ) (hi : i∈T) : (A i).card=1 := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    have eq : A (e x)={x} := by
      ext r
      simp [A,accepted,single,(cert x).2.1]
    simp [eq]
  have meet (i : ℕ) (hi : i∈S) : ∃ j,j<C.s ∧ ∃ v,(C.g j).op=.meet ∧
      (((C.g j).left=i ∧ (C.g j).right=v) ∨ ((C.g j).right=i ∧ (C.g j).left=v)) ∧
      k≤(A v).card := by
    have mem := Finset.mem_sdiff.mp hi
    have small : ¬2≤readers C.g C.s C.out i := fun h=>mem.2 (Finset.mem_filter.mpr ⟨mem.1,h⟩)
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp mem.1
    obtain ⟨j,b,q,op,stars⟩ := (cert x).2.2.resolve_left small
    refine ⟨j,q.valid,port (C.g j) (!b),op,?_,(G.degree x).trans (Finset.card_le_card ?_)⟩
    · cases b
      · exact Or.inr ⟨q.read,rfl⟩
      · exact Or.inl ⟨q.read,rfl⟩
    · exact fun y hy=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,stars y hy⟩
  let book := fun i=> if h : i∈S then (meet i h).choose else 0
  have picked (i : ℕ) (h : i∈S) : book i=(meet i h).choose := by simp [book,h]
  have need := demand m C.s k single C.X C.g S book hk
    (fun i hi=>thin i (Finset.mem_sdiff.mp hi).1)
    (fun i hi=>by rw [picked i hi]; exact (meet i hi).choose_spec.1)
    C.law C.bin (fun i hi=>by rw [picked i hi]; exact (meet i hi).choose_spec.2)
  apply IncidenceResidualEndLedger.endpoint_bound C.g m C.s C.out k W B S.card
  · rw [←population]; exact Finset.card_sdiff_add_card_eq_card subset
  · exact C.outBound
  · intro j hj; have h := C.earlier j hj; omega
  · exact live
  · intro i hi
    let x : Fin m := ⟨i,hi⟩
    have eq : A i={x} := by
      ext r
      change r∈(accepted m single C.X i) ↔ r∈({x}:Finset _)
      simp only [accepted,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      change ({r}:Mask m)∈C.X x.val ↔ r=x
      rw [C.raw]; simp [eq_comm]
    dsimp [W]; rw [eq,Finset.card_singleton]; omega
  · exact fun _ _=>Nat.min_le_left _ _
  · intro i hi
    have mem := Finset.mem_filter.mp hi
    obtain ⟨x,_,h⟩ := Finset.mem_image.mp mem.1
    refine ⟨h ▸ (cert x).1,?_,mem.2⟩
    dsimp [W]; rw [thin i mem.1]; omega
  · exact need

#print axioms lower
end IncidenceResidualLower
