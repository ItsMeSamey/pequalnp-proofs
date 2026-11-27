import IncidenceResidualPorts
import IncidenceResidualStar
namespace IncidenceResidualDemand
open CircuitRewire IncidenceResidualPorts
open scoped BigOperators

noncomputable def accepted {Z : Type*} (n : ℕ) (single : Fin n → Z) (X : ℕ → Set Z) (i : ℕ) :
    Finset (Fin n) := by classical exact Finset.univ.filter fun p => single p ∈ X i

theorem demand {Z : Type*} (n s k : ℕ) (single : Fin n → Z) (X : ℕ → Set Z)
    (g : ℕ → Gate) (S : Finset ℕ) (book : ℕ → ℕ) (hk : 1<k)
    (raw : ∀ x∈S,(accepted n single X x).card=1)
    (valid : ∀ x∈S,book x<s)
    (sem : ∀ j<s,X (n+j)=(g j).eval X)
    (bin : ∀ j<s,(g j).op=.join ∨ (g j).op=.meet)
    (paid : ∀ x∈S,∃ v,(g (book x)).op=.meet ∧
       (((g (book x)).left=x ∧ (g (book x)).right=v) ∨
        ((g (book x)).right=x ∧ (g (book x)).left=v)) ∧ k≤(accepted n single X v).card) :
    let W := fun i => min k (accepted n single X i).card
    k*S.card+(∑ j ∈ Finset.range s,W (n+j)) ≤
      ∑ j ∈ Finset.range s,(W (g j).left+W (g j).right) := by
  classical
  let A := accepted n single X
  let W := fun i => min k (A i).card
  let J := S.image book
  have sub (j : ℕ) (hj : j<s) : A (n+j) ⊆ A (g j).left ∪ A (g j).right := by
    intro p hp
    have h : single p ∈ X (n+j) := (Finset.mem_filter.mp hp).2
    rw [sem j hj] at h
    rcases bin j hj with op|op
    · change single p ∈ (g j).eval X at h
      simp only [Gate.eval,op,Op.eval,Set.mem_union] at h
      exact Finset.mem_union.mpr (h.imp (fun z=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,z⟩)
        (fun z=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,z⟩))
    · have z : single p∈X (g j).left := (show single p∈X (g j).left ∩ X (g j).right by
          simpa only [Gate.eval,op,Op.eval] using h).1
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z⟩)
  have inj : Set.InjOn book (↑S : Set ℕ) := by
    intro x hx y hy eq
    obtain ⟨v,_,p,large⟩ := paid x hx
    obtain ⟨w,_,q,_⟩ := paid y hy
    rw [←eq] at q
    have different : v≠y := by intro e; rw [e,raw y hy] at large; omega
    rcases p with ⟨l,r⟩|⟨r,l⟩ <;> rcases q with ⟨l',r'⟩|⟨r',l'⟩ <;> grind
  have each (j : ℕ) (hj : j∈Finset.range s) :
      (if j∈J then k else 0)+W (n+j)≤W (g j).left+W (g j).right := by
    have js := Finset.mem_range.mp hj
    split
    next mem =>
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp mem
      obtain ⟨v,kind,ports,large⟩ := paid x hx
      rw [eq] at kind ports
      have bound : A (n+j) ⊆ A x := by
        intro p hp
        have h := (Finset.mem_filter.mp hp).2
        change single p∈X (n+j) at h
        rw [sem j js] at h
        have z : single p∈X (g j).left ∩ X (g j).right := by simpa [Gate.eval,kind,Op.eval] using h
        rcases ports with ⟨l,_⟩|⟨r,_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,l ▸ z.1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,r ▸ z.2⟩
      have le := Finset.card_le_card bound
      change k ≤ (A v).card at large
      rcases ports with ⟨l,r⟩|⟨r,l⟩ <;> rw [l,r] <;> dsimp [W] <;> omega
    next =>
      have le := (Finset.card_le_card (sub j js)).trans (Finset.card_union_le _ _)
      dsimp [W]; omega
  have incl : J⊆Finset.range s := by
    intro j hj; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hj; exact Finset.mem_range.mpr (valid x hx)
  have cJ : J.card=S.card := Finset.card_image_of_injOn inj
  have count : (∑ j ∈ Finset.range s,if j∈J then k else 0)=k*S.card := by
    rw [← Finset.sum_filter]
    have filt : (Finset.range s).filter (fun j=>j∈J)=J := by ext j; simp; exact fun h=>Finset.mem_range.mp (incl h)
    simp [filt,cJ,Nat.mul_comm]
  have tot := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,count] at tot
  exact tot
#print axioms demand
end IncidenceResidualDemand
