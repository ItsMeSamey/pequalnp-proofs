import ThresholdSharedFlow
import ThresholdSharedPartition
import Mathlib.Data.Finset.Powerset
namespace ThresholdFlowPairs
open PEqualNP.CircuitLowerBounds ThresholdSimpleIncidence ThresholdOrExtraction T2OrPartition
open ThresholdSharedPartition ThresholdSharedFlow
variable {C : Circuit} {n : Nat} (L : Layout C n)
def hotPairs := ((hubs C n) ×ˢ (hubs C n)).filter
  (fun p => p.1≠p.2 ∧ active L p.1 p.2=true)
def unordered (p : Id C × Id C) : Finset (Id C) := {p.1,p.2}

theorem pair_budget (card : ∀ e, (endpoints L e).card=2)
    (inj : Function.Injective (endpoints L))
    (noedge : ∀ u∈hubs C n, ∀ v∈hubs C n, u≠v → active L u v=true →
      ∀ e : Fin n, u∈endpoints L e → v∉endpoints L e) :
    (hotPairs L).card+(internal L).card ≤ (hubs C n).card.choose 2 := by
  classical
  let H := hubs C n
  let A := (hotPairs L).image unordered
  let B := (internal L).image (endpoints L)
  have hp {p : Id C × Id C} (h : p∈hotPairs L) :
      (p.1∈H ∧ p.2∈H) ∧ p.1≠p.2 ∧ active L p.1 p.2=true := by simpa [hotPairs,H] using h
  have uniqueA : Set.InjOn (unordered (C:=C)) ((hotPairs L) : Set (Id C × Id C)) := by
    rintro ⟨a,b⟩ h ⟨x,y⟩ k eq
    have lt := oriented L (hp h).2.1 (hp h).2.2
    have lt' := oriented L (hp k).2.1 (hp k).2.2
    have hax : a=x ∨ a=y := by
      have z : a∈unordered (x,y) := eq ▸ (by simp [unordered] : a∈unordered (a,b))
      simpa [unordered] using z
    have hby : b=x ∨ b=y := by
      have z : b∈unordered (x,y) := eq ▸ (by simp [unordered] : b∈unordered (a,b))
      simpa [unordered] using z
    change a<b at lt
    change x<y at lt'
    rcases hax with ax|ay <;> rcases hby with bx|byy
    · exact False.elim (lt.ne (ax.trans bx.symm))
    · exact Prod.ext ax byy
    · have rev : b<a := by rw [bx,ay]; exact lt'
      exact False.elim (lt_asymm lt rev)
    · exact False.elim (lt.ne (ay.trans byy.symm))
  have internalH {e : Fin n} (he : e∈internal L) : endpoints L e ⊆ H := by
    have two : 2≤(hits L e).card := (Finset.mem_filter.mp he).2
    have eq : hits L e=endpoints L e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [card]; exact two)
    exact eq ▸ (Finset.inter_subset_right : hits L e⊆H)
  have sub : A ∪ B ⊆ H.powersetCard 2 := by
    intro t ht
    rcases Finset.mem_union.mp ht with ha|hb
    · obtain ⟨p,hp',rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset (hp hp').1.1
        (Finset.singleton_subset_iff.mpr (hp hp').1.2),Finset.card_pair_eq_two_iff.mpr (hp hp').2.1⟩
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_powersetCard.mpr ⟨internalH he,card e⟩
  have disj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro t hA hB
    obtain ⟨p,hp',ep⟩ := Finset.mem_image.mp hA
    obtain ⟨e,_,ee⟩ := Finset.mem_image.mp hB
    have eq := ee.trans ep.symm
    exact noedge p.1 (hp hp').1.1 p.2 (hp hp').1.2 (hp hp').2.1 (hp hp').2.2 e (by simp [eq,unordered]) (by simp [eq,unordered])
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint disj,Finset.card_powersetCard] at count
  simpa only [A,B,Finset.card_image_of_injOn uniqueA,Finset.card_image_of_injective _ inj,H] using count
end ThresholdFlowPairs
