import ThresholdUpperAverage
import Mathlib.Data.Nat.Factorial.Basic
namespace ThresholdUpperInjection
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/-- Successive unordered pairs on still-unused endpoints, in the order of
the new source vertices being exposed. -/
def partitions : Nat → Finset V → Finset (List (Finset V))
  | 0, _ => {[]}
  | k+1, U => ((U.powersetCard 2).sigma (fun e => partitions k (U \ e))).image
    (fun p => p.1 :: p.2)

def partitionCount : Nat → Nat → Nat
  | 0, _ => 1
  | k+1, n => n.choose 2 * partitionCount k (n-2)

theorem partitions_card (k : Nat) (U : Finset V) :
    (partitions k U).card=partitionCount k U.card := by
  induction k generalizing U with
  | zero => simp [partitions,partitionCount]
  | succ k ih =>
    have inj : Function.Injective (fun p : Σ _ : Finset V,List (Finset V) => p.1 :: p.2) := by
      rintro ⟨a,as⟩ ⟨b,bs⟩ eq
      cases eq
      rfl
    rw [partitions,Finset.card_image_of_injective _ inj,Finset.card_sigma,partitionCount]
    calc
      _ = ∑ _e∈U.powersetCard 2,partitionCount k (U.card-2) := by
        apply Finset.sum_congr rfl
        intro e he
        obtain ⟨sub,hc⟩ := Finset.mem_powersetCard.mp he
        rw [ih,Finset.card_sdiff_of_subset sub,hc]
      _ = _ := by simp [Finset.card_powersetCard]

theorem collision_constants :
    partitionCount 2 4=6 ∧ partitionCount 3 6=90 ∧ partitionCount 4 8=2520 := by decide

/-- Ordered distinct images drawn from a remaining finite edge alphabet. -/
def draws {A : Type*} [DecidableEq A] : Nat → Finset A → Finset (List A)
  | 0, _ => {[]}
  | k+1, E => (E.sigma (fun e => draws k (E.erase e))).image (fun p => p.1::p.2)

theorem draws_card {A : Type*} [DecidableEq A] (q : Nat) (E : Finset A) :
    (draws q E).card=E.card.descFactorial q := by
  induction q generalizing E with
  | zero => simp [draws]
  | succ q ih =>
    have inj : Function.Injective (fun p : Σ _ : A,List A => p.1 :: p.2) := by
      rintro ⟨a,as⟩ ⟨b,bs⟩ eq
      cases eq
      rfl
    rw [draws,Finset.card_image_of_injective _ inj,Finset.card_sigma]
    calc
      _ = ∑ _e∈E,(E.card-1).descFactorial q := by
        apply Finset.sum_congr rfl
        intro e he
        rw [ih,Finset.card_erase_of_mem he]
      _ = _ := by
        cases h : E.card with
        | zero => simp [h,Nat.descFactorial]
        | succ n =>
          rw [Nat.succ_descFactorial_succ]
          simp [h]

/-- A marked collection of completions after a fixed good first exposure.
Every legal colliding completion has all its edges supported on the remaining
2q endpoints, with no overlap. The ambient draw count is exact. -/
theorem conditional_count (q : Nat) (U : Finset V) (E : Finset (Finset V))
    (colliding : Finset (List (Finset V))) (ends : U.card=2*q)
    (disjointCover : colliding⊆partitions q U) :
    colliding.card≤partitionCount q (2*q) ∧ (draws q E).card=E.card.descFactorial q := by
  exact ⟨(Finset.card_le_card disjointCover).trans (by rw [partitions_card,ends]),draws_card _ _⟩

/-- At overlap three, the remaining two endpoints form the very edge already
used by the fourth input vertex from the first exposure. -/
theorem one_impossible (E : Finset (Finset V)) (u : Finset V) (used : u∉E)
    (x : Finset V) (fresh : x∈E) (full : x=u) : False := used (full ▸ fresh)
/-- Physical test sufficient for the partition envelope: each fresh edge is an
unordered two-set and the fresh edges are pairwise vertex-disjoint. -/
theorem mem_partitions (U : Finset V) (xs : List (Finset V))
    (pairs : ∀ e∈xs, e.card=2 ∧ e⊆U)
    (dis : xs.Pairwise Disjoint) : xs∈partitions xs.length U := by
  induction xs generalizing U with
  | nil => simp [partitions]
  | cons e es ih =>
    have eprop := pairs e (by simp)
    obtain ⟨apart,recDis⟩ := List.pairwise_cons.mp dis
    have rest : es∈partitions es.length (U \ e) := by
      apply ih _ _ recDis
      intro a ha
      have h := pairs a (List.mem_cons_of_mem _ ha)
      refine ⟨h.1,fun v hv => Finset.mem_sdiff.mpr ⟨h.2 hv,?_⟩⟩
      exact fun he => Finset.disjoint_left.mp (apart a ha) he hv
    apply Finset.mem_image.mpr
    exact ⟨⟨e,es⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨eprop.2,eprop.1⟩,rest⟩,rfl⟩

theorem collision_envelope (q : Nat) (allEnds sharedEnds : Finset V)
    (colliding : Finset (List (Finset V)))
    (len : ∀ xs∈colliding,xs.length=q)
    (size : ∀ xs∈colliding,∀ e∈xs,e.card=2 ∧ e⊆allEnds ∧ Disjoint e sharedEnds)
    (dis : ∀ xs∈colliding,xs.Pairwise Disjoint)
    (remaining : (allEnds \ sharedEnds).card=2*q) :
    colliding.card≤partitionCount q (2*q) := by
  have sub : colliding⊆partitions q (allEnds \ sharedEnds) := by
    intro xs hx
    rw [←len xs hx]
    apply mem_partitions _ _ _ (dis xs hx)
    intro e he
    obtain ⟨sz,all,apart⟩ := size xs hx e he
    exact ⟨sz,fun v hv => Finset.mem_sdiff.mpr ⟨all hv,Finset.disjoint_left.mp apart hv⟩⟩
  exact (Finset.card_le_card sub).trans (by rw [partitions_card,remaining])

end ThresholdUpperInjection
