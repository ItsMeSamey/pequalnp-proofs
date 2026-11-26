import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators
open Classical
namespace ThresholdUpperExtension
variable {A P Q B : Type*} [Fintype A] [Fintype P] [Fintype Q] [Fintype B]

/-- Select and order any exposed coordinates. Every event may use a different
coordinate order, since all full labelled injections are counted once. -/
def splitInj (s : A ≃ P ⊕ Q) :
    (A ↪ B) ≃ (Σ f : P ↪ B, Q ↪ ↥(Set.range f)ᶜ) :=
  (Equiv.embeddingCongr s (Equiv.refl B)).trans Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

theorem exposed (s : A ≃ P ⊕ Q) (f : A ↪ B) (p : P) :
    ((splitInj s f).1) p=f (s.symm (Sum.inl p)) := rfl

noncomputable def eventEquiv (s : A ≃ P ⊕ Q) (event : Finset (P ↪ B)) :
    {u : A ↪ B // (splitInj s u).1∈event} ≃
      (Σ f : ↥event, Q ↪ ↥(Set.range f.val)ᶜ) := by
  let e := splitInj (B:=B) s
  refine { toFun := fun u => ⟨⟨(e u.val).1,u.property⟩,(e u.val).2⟩
           invFun := fun z => ⟨e.symm ⟨z.1.val,z.2⟩,?_⟩
           left_inv := fun z => Subtype.ext (e.symm_apply_apply z.val)
           right_inv := ?_ }
  · change (e (e.symm _)).1∈event
    rw [e.apply_symm_apply]
    exact z.1.property
  · rintro ⟨⟨f,hf⟩,g⟩
    have inj : Function.Injective (fun z : Σ u : ↥event, Q ↪ ↥(Set.range u.val)ᶜ =>
        (⟨z.1.val,z.2⟩ : Σ u : P ↪ B, Q ↪ ↥(Set.range u)ᶜ)) := by
      rintro ⟨⟨u,hu⟩,a⟩ ⟨⟨v,hv⟩,b⟩ h
      cases h
      rfl
    apply inj
    exact e.apply_symm_apply ⟨f,g⟩

theorem full_count (s : A ≃ P ⊕ Q) (event : Finset (P ↪ B))
    [Fintype {u : A ↪ B // (splitInj s u).1∈event}] :
    Fintype.card {u : A ↪ B // (splitInj s u).1∈event} =
      event.card*(Fintype.card B-Fintype.card P).descFactorial (Fintype.card Q) := by
  classical
  rw [Fintype.card_congr (eventEquiv s event),Fintype.card_sigma]
  simp only [Fintype.card_embedding_eq,Fintype.card_compl_set,Fintype.card_range,
    Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id]

/-- No division assumptions, including empty prefix sets. Every partial event
has the same proportion in the full sample if the respective totals are nonzero. -/
theorem proportion (s : A ≃ P ⊕ Q) (event : Finset (P ↪ B)) :
    (Finset.univ.filter (fun u : A ↪ B => (splitInj s u).1∈event)).card *
      Fintype.card (P ↪ B) = event.card*Fintype.card (A ↪ B) := by
  classical
  have count (D : Finset (P ↪ B)) :
      (Finset.univ.filter (fun u : A ↪ B => (splitInj s u).1∈D)).card=
      D.card*(Fintype.card B-Fintype.card P).descFactorial (Fintype.card Q) := by
    rw [←Fintype.card_of_subtype _ (show ∀ u : A ↪ B, u∈Finset.univ.filter (fun f => (splitInj s f).1∈D) ↔ (splitInj s u).1∈D from fun u => by simp)]
    exact full_count s D
  have total := count Finset.univ
  simp only [Finset.mem_univ,Finset.filter_true,Finset.card_univ] at total
  rw [count,total]
  ring
/-- The next event may depend on the values of all previously exposed images.
Its section cardinalities are added across those first exposures. -/
theorem section_count (s : A ≃ P ⊕ Q)
    (allowed : (f : P ↪ B) → Finset (Q ↪ ↥(Set.range f)ᶜ)) :
    (Finset.univ.filter (fun u : A ↪ B => (splitInj s u).2∈allowed (splitInj s u).1)).card =
      ∑ f : P ↪ B,(allowed f).card := by
  classical
  let e := splitInj (B:=B) s
  let D := Finset.univ.sigma allowed
  let event := Finset.univ.filter (fun u : A ↪ B => (e u).2∈allowed (e u).1)
  have eq : event.map e.toEmbedding=D := by
    ext z
    constructor
    · intro hz
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hu).2⟩
    · intro hz
      have membership := (Finset.mem_sigma.mp hz).2
      exact Finset.mem_map.mpr ⟨e.symm z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [e.apply_symm_apply]; exact membership⟩,e.apply_symm_apply _⟩
  change event.card=_
  rw [←Finset.card_sigma]
  simpa [D] using congrArg Finset.card eq

/-- Two exposures followed by unrestricted labelled completion. A conditional
q-image collision event may use the actual four previously fixed edge images. -/
theorem conditional_mass {X Y : Type*} [Fintype X] [Fintype Y]
    (s : A ≃ P ⊕ Q) (next : Q ≃ X ⊕ Y)
    (bad : (f : P ↪ B) → Finset (X ↪ ↥(Set.range f)ᶜ))
    (cap : Nat) (bound : ∀ f,(bad f).card≤cap) :
    let sec := fun f : P ↪ B => Finset.univ.filter (fun g : Q ↪ ↥(Set.range f)ᶜ =>
      (splitInj next g).1∈bad f)
    (Finset.univ.filter (fun u : A ↪ B => (splitInj s u).2∈sec (splitInj s u).1)).card ≤
      Fintype.card (P ↪ B)*cap*
      ((Fintype.card B-Fintype.card P)-Fintype.card X).descFactorial (Fintype.card Y) := by
  classical
  intro sec
  rw [section_count]
  let mult := ((Fintype.card B-Fintype.card P)-Fintype.card X).descFactorial (Fintype.card Y)
  have each (f : P ↪ B) : (sec f).card≤cap*mult := by
    have exactN := full_count next (bad f)
    have cnt := Fintype.card_of_subtype (sec f) (p:=fun g => (splitInj next g).1∈bad f)
      (by intro g; simp [sec])
    rw [←cnt,exactN]
    simp only [Fintype.card_compl_set,Fintype.card_range,mult]
    exact Nat.mul_le_mul_right _ (bound f)
  have total := Finset.sum_le_sum (fun f (_ : f∈Finset.univ) => each f)
  simpa [mult,Nat.mul_assoc] using total
end ThresholdUpperExtension
