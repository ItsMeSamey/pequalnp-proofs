import ThresholdUpperEventGeometry
namespace ThresholdUpperPostImages
open scoped BigOperators
open ThresholdUpperSecond ThresholdUpperInjection
open Classical
variable {P X : Type*} [Fintype P] [Fintype X] {z : Nat}

def xy (f : P ↪ Edges z) (g : X ↪ ↥(Set.range f)ᶜ) (x : X) : Finset (Fin z) := (g x).val.val

/-- Injectively encode each fresh ordered exposure by the list of its edges.
Unordered endpoint pairs stay unordered, so no extra factor 2^q appears. -/
def encode (f : P ↪ Edges z) (order : Fin q ≃ X) (g : X ↪ ↥(Set.range f)ᶜ) :=
  List.ofFn (fun i => xy f g (order i))

theorem encode_inj (f : P ↪ Edges z) (order : Fin q ≃ X) : Function.Injective (encode f order) := by
  intro a b eq
  apply DFunLike.ext
  intro x
  have valEq := (List.ofFn_injective eq)
  have hit := congrFun valEq (order.symm x)
  apply Subtype.ext
  apply Subtype.ext
  change xy f a x = xy f b x
  simpa only [Equiv.apply_symm_apply] using hit

noncomputable def allowed (f : P ↪ Edges z) (sites : Finset (Fin z)) :
    Finset (X ↪ ↥(Set.range f)ᶜ) := Finset.univ.filter (fun g =>
      (∀ x,xy f g x⊆sites) ∧ Pairwise (fun x y => Disjoint (xy f g x) (xy f g y)))

theorem allowed_card (f : P ↪ Edges z) (sites : Finset (Fin z)) (q : Nat)
    (order : Fin q ≃ X) (size : sites.card=2*q) :
    (allowed (X:=X) f sites).card≤partitionCount q (2*q) := by
  classical
  have incl : ((allowed f sites).image (encode f order))⊆partitions q sites := by
    intro xs h
    obtain ⟨g,good,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨inside,apart⟩ := (Finset.mem_filter.mp good).2
    have len : (encode f order g).length=q := by simp [encode]
    apply (congrArg (fun d => encode f order g ∈ partitions d sites) len).mp
    apply mem_partitions
    · intro e he
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
      subst e
      exact ⟨(Finset.mem_powersetCard.mp (g (order i)).val.property).2,inside _⟩
    · rw [encode,List.pairwise_ofFn]
      intro i j hij
      exact apart (order.injective.ne (ne_of_lt hij))
  rw [←Finset.card_image_of_injective _ (encode_inj f order)]
  exact (Finset.card_le_card incl).trans (by rw [partitions_card,size])
end ThresholdUpperPostImages
