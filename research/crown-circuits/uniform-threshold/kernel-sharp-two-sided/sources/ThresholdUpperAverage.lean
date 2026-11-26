import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
open scoped BigOperators
namespace ThresholdUpperAverage
variable {T : Type*} [DecidableEq T]

/-- A single good object meets the sum of all nonnegative loss charges.
The denominator uses the number certified good by a separate union bound. -/
theorem choose_good (sample bad : Finset T) (loss : T → Nat) (b A : Nat)
    (positive : b<sample.card) (tail : bad.card≤b)
    (budget : (∑ x∈sample, loss x)≤A) :
    ∃ x∈sample \ bad, (sample.card-b)*loss x≤A := by
  classical
  let G := sample \ bad
  have cov : sample⊆G∪bad := by
    intro x hx
    by_cases mem : x∈bad
    · exact Finset.mem_union_right _ mem
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx,mem⟩)
  have cnt := (Finset.card_le_card cov).trans (Finset.card_union_le _ _)
  have sz : sample.card-b≤G.card := by omega
  have hf : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x,hx,minimal⟩ := Finset.exists_min_image G loss hf
  have best : G.card*loss x≤∑ y∈G,loss y := by
    calc
      _ = ∑ _y∈G,loss x := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun y hy => minimal y hy)
  refine ⟨x,hx,?_⟩
  exact ((Nat.mul_le_mul_right _ sz).trans best).trans
    ((Finset.sum_le_sum_of_subset (Finset.sdiff_subset : G⊆sample)).trans budget)

/-- Counting the uniform fixed-size sample by deleting the prescribed edges.
Works for arbitrary finite edge names, including the boundary k>N. -/
theorem pattern_count (U D : Finset T) (v : Nat) (inside : D⊆U) (fit : D.card≤v) :
    ((U.powersetCard v).filter (fun R => D⊆R)).card =
      (U.card-D.card).choose (v-D.card) := by
  classical
  let A := (U.powersetCard v).filter (fun R => D⊆R)
  let B := (U \ D).powersetCard (v-D.card)
  have corr : A.card=B.card := by
    apply Finset.card_bij (fun R _ => R \ D)
    · intro R hR
      obtain ⟨pool,sub⟩ := Finset.mem_filter.mp hR
      obtain ⟨ru,card⟩ := Finset.mem_powersetCard.mp pool
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_,by rw [Finset.card_sdiff_of_subset sub,card]⟩
      intro e he
      obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨ru hr,hn⟩
    · intro R hR S hS eq
      have rd := (Finset.mem_filter.mp hR).2
      have sd := (Finset.mem_filter.mp hS).2
      ext e
      by_cases ed : e∈D
      · exact ⟨fun _ => sd ed,fun _ => rd ed⟩
      · have h := congrArg (fun X : Finset T => e∈X) eq
        simpa [ed] using h.to_iff
    · intro S hS
      obtain ⟨inc,card⟩ := Finset.mem_powersetCard.mp hS
      have dis : Disjoint S D := Finset.disjoint_left.mpr (fun e he hd =>
        (Finset.mem_sdiff.mp (inc he)).2 hd)
      refine ⟨S∪D,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_,?_⟩,
        Finset.subset_union_right⟩,?_⟩
      · intro e h
        rcases Finset.mem_union.mp h with s|d
        · exact (Finset.mem_sdiff.mp (inc s)).1
        · exact inside d
      · rw [Finset.card_union_of_disjoint dis,card]; omega
      · ext e
        by_cases ed : e∈D
        · simp [ed,show e∉S from fun es => Finset.disjoint_left.mp dis es ed]
        · simp [ed]
  simpa [A,B,Finset.card_powersetCard,Finset.card_sdiff_of_subset inside] using corr
theorem exposure {J : Type*} [DecidableEq J] (U : Finset T) (index : Finset J)
    (edges : J → Finset T) (j v : Nat) (fit : j≤v)
    (incl : ∀ i∈index, edges i⊆U) (size : ∀ i∈index,(edges i).card=j) :
    (∑ R∈U.powersetCard v,(index.filter (fun i => edges i⊆R)).card) =
       index.card*(U.card-j).choose (v-j) := by
  classical
  calc
    _ = ∑ R∈U.powersetCard v, ∑ i∈index, if edges i⊆R then 1 else 0 := by simp
    _ = ∑ i∈index, ∑ R∈U.powersetCard v, if edges i⊆R then 1 else 0 := Finset.sum_comm
    _ = ∑ _i∈index, (U.card-j).choose (v-j) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := pattern_count U (edges i) v (incl i hi) ((size i hi).trans_le fit)
      simpa [size i hi] using h
    _ = _ := by simp

theorem first_selection {J₂ J₄ Jk : Type*} [DecidableEq J₂] [DecidableEq J₄] [DecidableEq Jk]
    (U : Finset T) (v k : Nat) (four : 4≤v) (kf : k≤v)
    (W : Finset J₂) (C : Finset J₄) (S : Finset Jk)
    (wedge : J₂ → Finset T) (cycle : J₄ → Finset T) (star : Jk → Finset T)
    (wp : ∀ i∈W,wedge i⊆U ∧ (wedge i).card=2)
    (cp : ∀ i∈C,cycle i⊆U ∧ (cycle i).card=4)
    (sp : ∀ i∈S,star i⊆U ∧ (star i).card=k)
    (room : S.card*(U.card-k).choose (v-k)<U.card.choose v) :
    ∃ R∈U.powersetCard v, (∀ i∈S, ¬star i⊆R) ∧
      (U.card.choose v-S.card*(U.card-k).choose (v-k))*
      ((W.filter (fun i => wedge i⊆R)).card+(C.filter (fun i => cycle i⊆R)).card) ≤
      W.card*(U.card-2).choose (v-2)+C.card*(U.card-4).choose (v-4) := by
  classical
  let sample := U.powersetCard v
  let bad := sample.filter (fun R => ∃ i∈S, star i⊆R)
  have w := exposure U W wedge 2 v (by omega) (fun i hi => (wp i hi).1) (fun i hi => (wp i hi).2)
  have c := exposure U C cycle 4 v four (fun i hi => (cp i hi).1) (fun i hi => (cp i hi).2)
  have s := exposure U S star k v kf (fun i hi => (sp i hi).1) (fun i hi => (sp i hi).2)
  have bc : bad.card≤S.card*(U.card-k).choose (v-k) := by
    rw [←s]
    calc
      _ = ∑ R∈sample, if ∃ i∈S,star i⊆R then (1 : Nat) else 0 := by simp [bad]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro R _
        split
        · rename_i h
          obtain ⟨i,hi,ok⟩ := h
          exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,ok⟩⟩
        · exact Nat.zero_le _
  obtain ⟨R,hr,loss⟩ := choose_good sample bad
    (fun R => (W.filter (fun i => wedge i⊆R)).card+(C.filter (fun i => cycle i⊆R)).card)
    _ (W.card*(U.card-2).choose (v-2)+C.card*(U.card-4).choose (v-4))
    (by simpa [sample] using room) bc (by
      simpa only [sample,Finset.sum_add_distrib,w,c] using
        (le_refl (W.card*(U.card-2).choose (v-2)+C.card*(U.card-4).choose (v-4))))
  obtain ⟨mem,good⟩ := Finset.mem_sdiff.mp hr
  exact ⟨R,mem,fun i hi ok => good (Finset.mem_filter.mpr ⟨mem,i,hi,ok⟩),by simpa [sample] using loss⟩
end ThresholdUpperAverage
