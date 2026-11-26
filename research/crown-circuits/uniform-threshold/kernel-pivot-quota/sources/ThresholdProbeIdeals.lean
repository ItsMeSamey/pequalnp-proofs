import ThresholdFlowPairs
namespace ThresholdProbeIdeals
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
def predOf (Q : Finset (V×V)) (H : Finset V) :=
  Finset.univ.filter (fun a => ∃ b∈H,(a,b)∈Q)
def Ideal (Q : Finset (V×V)) (I : Finset V) : Prop :=
  ∀ a b, (a,b)∈Q → b∈I → a∈I
def Cut (Q : Finset (V×V)) (I : Finset V) :=
  Q.filter (fun p => p.1∈I ∧ p.2∉I)
def Touch (Q : Finset (V×V)) (H : Finset V) :=
  Q.filter (fun p => p.1∈H ∨ p.2∈H)
def Anti (Q : Finset (V×V)) (H : Finset V) :=
  ∀ a∈H,∀ b∈H,(a,b)∉Q
def Trans (Q : Finset (V×V)) :=
  ∀ a b c, (a,b)∈Q → (b,c)∈Q → (a,c)∈Q

theorem ideal_pair (Q : Finset (V×V)) (H : Finset V) (tr : Trans Q) (anti : Anti Q H) :
    let I := predOf Q H
    Ideal Q I ∧ Disjoint I H ∧ Ideal Q (I∪H) ∧ Touch Q H ⊆ Cut Q I ∪ Cut Q (I∪H) := by
  classical
  intro I
  have member (a : V) : a∈I ↔ ∃ b∈H,(a,b)∈Q := by simp [I,predOf]
  have closed : Ideal Q I := by
    intro a b ab hb
    obtain ⟨c,hc,bc⟩ := (member b).mp hb
    exact (member a).mpr ⟨c,hc,tr a b c ab bc⟩
  have dis : Disjoint I H := Finset.disjoint_left.mpr (by
    intro a ha ah
    obtain ⟨b,bh,ab⟩ := (member a).mp ha
    exact anti a ah b bh ab)
  refine ⟨closed,dis,?_,?_⟩
  · intro a b ab hb
    apply Finset.mem_union.mpr
    rcases Finset.mem_union.mp hb with bi|bh
    · exact Or.inl (closed a b ab bi)
    · exact Or.inl ((member a).mpr ⟨b,bh,ab⟩)
  · rintro ⟨a,b⟩ hp
    obtain ⟨ab,hit⟩ := Finset.mem_filter.mp hp
    change a∈H ∨ b∈H at hit
    apply Finset.mem_union.mpr
    rcases hit with ah|bh
    · right
      apply Finset.mem_filter.mpr
      refine ⟨ab,Finset.mem_union_right _ ah,?_⟩
      intro inB
      rcases Finset.mem_union.mp inB with bi|bh
      · exact Finset.disjoint_left.mp dis (closed a b ab bi) ah
      · exact anti a ah b bh ab
    · left
      exact Finset.mem_filter.mpr ⟨ab,(member a).mpr ⟨b,bh,ab⟩,
        fun bi => Finset.disjoint_left.mp dis bi bh⟩

theorem touch_bound (Q : Finset (V×V)) (H : Finset V) (tr : Trans Q) (anti : Anti Q H)
    (B : Nat) (budget : ∀ I,Ideal Q I → (Cut Q I).card≤B) : (Touch Q H).card≤2*B := by
  rcases ideal_pair Q H tr anti with ⟨c1,_,c2,sub⟩
  have h := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have h1 := budget _ c1
  have h2 := budget _ c2
  omega

theorem high_anti (Q : Finset (V×V)) (hubs : Finset V) (nbr : V → Finset V)
    (inside : ∀ v, nbr v ⊆ hubs)
    (separate : ∀ a b,(a,b)∈Q → Disjoint (nbr a) (nbr b)) :
    Anti Q (hubs.filter (fun a => hubs.card<2*(nbr a).card)) := by
  intro a ha b hb pair
  have da := (Finset.mem_filter.mp ha).2
  have db := (Finset.mem_filter.mp hb).2
  have cap := Finset.card_le_card (Finset.union_subset (inside a) (inside b))
  rw [Finset.card_union_of_disjoint (separate a b pair)] at cap
  omega
def succCount (Q : Finset (V×V)) (a : V) := (Q.filter (fun p => p.1=a)).card
def predCount (Q : Finset (V×V)) (a : V) := (Q.filter (fun p => p.2=a)).card

theorem cut_balance (Q : Finset (V×V)) (I : Finset V) (closed : Ideal Q I) :
    (Cut Q I).card + ∑ a∈I,predCount Q a = ∑ a∈I,succCount Q a := by
  classical
  have expand (f : V×V → V) :
      (∑ a∈I,(Q.filter (fun p => f p=a)).card) =
      ∑ p∈Q, (if f p∈I then 1 else 0 : Nat) := by
    calc
      _ = ∑ a∈I, ∑ p∈Q, (if f p=a then 1 else 0 : Nat) := by
        apply Finset.sum_congr rfl; intro a _
        simp [Finset.sum_boole]
      _ = _ := by rw [Finset.sum_comm]; simp
  change _ + (∑ a∈I,(Q.filter (fun p => p.2=a)).card) =
    ∑ a∈I,(Q.filter (fun p => p.1=a)).card
  rw [expand Prod.snd,expand Prod.fst]
  have localEq (p : V×V) (hp : p∈Q) :
      (if p.1∈I ∧ p.2∉I then 1 else 0 : Nat) + (if p.2∈I then 1 else 0) =
      (if p.1∈I then 1 else 0) := by
    by_cases b : p.2∈I
    · simp [b,closed p.1 p.2 hp b]
    · simp [b]
  have sums := Finset.sum_congr (s₁:=Q) rfl localEq
  simpa only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id,Cut] using sums

theorem cut_budget (Q : Finset (V×V)) (I : Finset V) (closed : Ideal Q I)
    (D : V → Nat) (C : Nat)
    (point : ∀ a∈I,succCount Q a≤predCount Q a+D a+C) :
    (Cut Q I).card≤(∑ a∈I,D a)+I.card*C := by
  have t := Finset.sum_le_sum point
  have balance := cut_balance Q I closed
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at t
  omega

#print axioms touch_bound
#print axioms cut_balance
#print axioms high_anti
end ThresholdProbeIdeals
