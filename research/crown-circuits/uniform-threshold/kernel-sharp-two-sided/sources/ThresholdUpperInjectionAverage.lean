import ThresholdUpperInjection
namespace ThresholdUpperInjectionAverage
open scoped BigOperators
variable {I B : Type*} [DecidableEq I] [DecidableEq B]

/-- Distinct four-sets that share a pair are counted by the incidences of
pairs in their common coordinate. The estimate is sharp enough when a pair
occurs in at most d boxes. -/
theorem pair_load (pairs : Finset I) (codeg : I→Nat) (d f : Nat)
    (cap : ∀ i∈pairs,codeg i≤d) (total : (∑ i∈pairs,codeg i)=6*f) :
    (∑ i∈pairs,(codeg i).choose 2)≤3*f*d := by
  have one (z : Nat) : 2*z.choose 2=z*(z-1) := by
    cases z with
    | zero => decide
    | succ k =>
      induction k with
      | zero => decide
      | succ j ih =>
        rw [Nat.choose_succ_succ]
        simp only [Nat.choose_one_right]
        simp only [Nat.succ_sub_one] at *
        nlinarith
  have each (i) (hi : i∈pairs) : 2*(codeg i).choose 2≤d*codeg i := by
    have h := cap i hi
    rw [one,Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (by omega : codeg i-1≤d)
  have all := Finset.sum_le_sum each
  rw [←Finset.mul_sum,←Finset.mul_sum,total] at all
  nlinarith

private theorem layer {A : Type*} [DecidableEq A] (sample : Finset I) (den : Nat) (indexes : Finset A) (pred : A→I→Prop)
      [∀ a i, Decidable (pred a i)] (lim : Nat)
      (h : ∀ a∈indexes,den*(sample.filter (pred a)).card≤lim) :
      (∑ i∈sample,den*(indexes.filter (fun a => pred a i)).card)≤indexes.card*lim := by
    have flip :
        (∑ i∈sample,(indexes.filter (fun a => pred a i)).card)=
        ∑ a∈indexes,(sample.filter (pred a)).card := by
      calc
        _ = ∑ i∈sample,∑ a∈indexes,if pred a i then (1:Nat) else 0 := by simp
        _ = ∑ a∈indexes,∑ i∈sample,if pred a i then (1:Nat) else 0 := Finset.sum_comm
        _ = _ := by simp
    rw [←Finset.mul_sum,flip,Finset.mul_sum]
    simpa using Finset.sum_le_sum h

/-- Atomic counting bounds are multiplied by a common denominator. Each bad
box or coincident unordered pair is an event. An averaged sample meets the
sum across the three event families simultaneously. -/
theorem choose_injection {J K : Type*} [DecidableEq J] [DecidableEq K]
    (sample : Finset I) (fail : Finset B) (two : Finset J) (other : Finset K)
    (p₁ : B→I→Prop) (p₂ : J→I→Prop) (p₃ : K→I→Prop)
    [∀ a i, Decidable (p₁ a i)] [∀ a i, Decidable (p₂ a i)] [∀ a i, Decidable (p₃ a i)]
    (den b c d : Nat) (nonempty : sample.Nonempty)
    (m₁ : ∀ a∈fail,den*(sample.filter (p₁ a)).card≤b)
    (m₂ : ∀ a∈two,den*(sample.filter (p₂ a)).card≤c)
    (m₃ : ∀ a∈other,den*(sample.filter (p₃ a)).card≤d) :
    ∃ i∈sample,sample.card*den*
      ((fail.filter (fun a => p₁ a i)).card+(two.filter (fun a => p₂ a i)).card+
      (other.filter (fun a => p₃ a i)).card)≤fail.card*b+two.card*c+other.card*d := by
  classical
  let cost := fun i => (fail.filter (fun a => p₁ a i)).card+
    (two.filter (fun a => p₂ a i)).card+(other.filter (fun a => p₃ a i)).card
  obtain ⟨i,hi,least⟩ := Finset.exists_min_image sample cost nonempty
  have low : sample.card*(den*cost i)≤∑ t∈sample,den*cost t := by
    calc
      _ = ∑ _∈sample,den*cost i := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht => Nat.mul_le_mul_left den (least t ht))
  have high := Nat.add_le_add (Nat.add_le_add (layer sample den fail p₁ b m₁) (layer sample den two p₂ c m₂))
      (layer sample den other p₃ d m₃)
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib] at high
  have hiCost : (∑ t∈sample,den*cost t)≤fail.card*b+two.card*c+other.card*d := by simpa [cost,Nat.mul_add] using high
  exact ⟨i,hi,by simpa [cost,Nat.mul_assoc] using low.trans hiCost⟩
end ThresholdUpperInjectionAverage
