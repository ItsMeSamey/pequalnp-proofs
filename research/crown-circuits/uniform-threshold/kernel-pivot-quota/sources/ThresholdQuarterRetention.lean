import ThresholdQuarterCubes
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
namespace ThresholdQuarterRetention
open ThresholdQuarterCubes
open private force fits_force from ThresholdQuarterCubes
variable {I R : Type*} [Fintype I] [DecidableEq I] [DecidableEq R]
noncomputable def retained (rows : Finset R) (pins : R→TwoPins I) (f : I→Bool) :=
  by classical exact rows.filter (fun r => Fits (pins r) f)

theorem exists_retains (rows : Finset R) (pins : R→TwoPins I) :
    ∃ f,rows.card≤4*(retained rows pins f).card := by
  classical
  let A := Finset.univ (α:=I→Bool)
  let B := A.sigma (fun f => retained rows pins f)
  let enc := fun p : R×(I→Bool) =>
    ((⟨force (pins p.1) p.2,p.1⟩ : Sigma (fun _ : I→Bool => R)),
      (p.2 (pins p.1).first,p.2 (pins p.1).second))
  have hits (p) (hp : p∈rows ×ˢ A) : enc p ∈ B ×ˢ (Finset.univ : Finset (Bool×Bool)) := by
    obtain ⟨hr,_⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hr,fits_force _ _⟩⟩,Finset.mem_univ _⟩
  have inject : Set.InjOn enc (↑(rows ×ˢ A)) := by
    rintro ⟨r,f⟩ _ ⟨s,g⟩ _ eq
    have rs : r=s := congrArg (fun p => p.1.2) eq
    subst s
    have ff : force (pins r) f=force (pins r) g := congrArg (fun p => p.1.1) eq
    have bits : (f (pins r).first,f (pins r).second)=(g (pins r).first,g (pins r).second) := congrArg Prod.snd eq
    have fg : f=g := by
      funext i
      by_cases one : i=(pins r).first
      · simpa only [one] using congrArg Prod.fst bits
      by_cases two : i=(pins r).second
      · simpa only [two] using congrArg Prod.snd bits
      simpa [force,one,two] using congrFun ff i
    rw [fg]
  have bound := Finset.card_le_card_of_injOn enc hits inject
  have nonempty : A.Nonempty := ⟨fun _ => false,Finset.mem_univ _⟩
  obtain ⟨f,hf,best⟩ := Finset.exists_max_image A (fun f => (retained rows pins f).card) nonempty
  refine ⟨f,?_⟩
  have avg : B.card ≤ A.card * (retained rows pins f).card := by
    rw [show B.card=∑ g∈A,(retained rows pins g).card from Finset.card_sigma _ _]
    simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using Finset.sum_le_sum best
  have cap : (Finset.univ : Finset (Bool×Bool)).card=4 := by decide
  rw [Finset.card_product,Finset.card_product,cap] at bound
  apply Nat.le_of_mul_le_mul_right _ (Finset.card_pos.mpr nonempty)
  calc
    _ ≤ B.card*4 := bound
    _ ≤ (A.card*(retained rows pins f).card)*4 := Nat.mul_le_mul_right _ avg
    _ = _ := by ac_rfl

/-- E is the ordinary family of across-AND two-private rows. After removing
at most a same-AND rows, this gives the finite binomial bound. -/
theorem finite_bound (rows : Finset R) (pins : R→TwoPins I)
    (actual : Finset (Finset R)) (L : Nat)
    (holes : (rows.powersetCard 2 \ actual).card≤L)
    (one : ∀ f, ((retained rows pins f).powersetCard 2 ∩ actual).card≤1) :
    ∃ t : Nat, rows.card≤4*t ∧ t.choose 2≤L+1 := by
  classical
  obtain ⟨f,hf⟩ := exists_retains rows pins
  let S := retained rows pins f
  refine ⟨S.card,hf,?_⟩
  have sub : S⊆rows := Finset.filter_subset _ _
  have absent : S.powersetCard 2 \ actual ⊆ rows.powersetCard 2 \ actual := by
    intro p hp
    obtain ⟨mem,no⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨incl,size⟩ := Finset.mem_powersetCard.mp mem
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨fun i hi => sub (incl hi),size⟩,no⟩
  have bound := (Finset.card_le_card absent).trans holes
  have split := Finset.card_sdiff_add_card_inter (S.powersetCard 2) actual
  have present := one f
  rw [Finset.card_powersetCard] at split
  change (S.powersetCard 2 ∩ actual).card≤1 at present
  omega
end ThresholdQuarterRetention

namespace ThresholdQuarterRetention
variable {I R V : Type*} [DecidableEq I] [DecidableEq V] [DecidableEq R]

/-- If two distinct receiver wires end at one physical binary gate, they
occupy its two opposite pins. A simple row signature charges that gate once. -/
theorem same_gate_bound (rows : Finset R) (ands : Finset I) (left right : R→V)
    (site : V→I×Bool) (andSite : ∀ r∈rows,(site (left r)).1∈ands)
    (distinct : ∀ r∈rows,left r≠right r) (uniqueSite : Function.Injective site)
    (simple : Set.InjOn (fun r => ({left r,right r} : Finset V)) ↑rows) :
    (rows.filter (fun r => (site (left r)).1=(site (right r)).1)).card≤ands.card := by
  classical
  let same := rows.filter (fun r => (site (left r)).1=(site (right r)).1)
  have cover (r) (hr : r∈same) (v : V) (meet : (site v).1=(site (left r)).1) :
      v∈({left r,right r} : Finset V) := by
    obtain ⟨row,sameGate⟩ := Finset.mem_filter.mp hr
    have bits : (site (left r)).2≠(site (right r)).2 := fun eq =>
      distinct r row (uniqueSite (Prod.ext sameGate eq))
    by_cases b : (site v).2=(site (left r)).2
    · have e : v=left r := uniqueSite (Prod.ext meet b)
      simp [e]
    · have vright : (site v).2=(site (right r)).2 := by
        cases bl : (site (left r)).2 <;> cases br : (site (right r)).2 <;>
          cases bv : (site v).2 <;> simp_all
      have e : v=right r := uniqueSite (Prod.ext (meet.trans sameGate) vright)
      simp [e]
  apply Finset.card_le_card_of_injOn (fun r => (site (left r)).1)
    (fun r h => andSite r (Finset.mem_filter.mp h).1)
  intro r hr s hs eq
  apply simple (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hs).1
  apply Finset.Subset.antisymm
  · apply Finset.insert_subset (cover s hs _ eq)
    exact Finset.singleton_subset_iff.mpr (cover s hs _ ((Finset.mem_filter.mp hr).2.symm.trans eq))
  · apply Finset.insert_subset (cover r hr _ eq.symm)
    exact Finset.singleton_subset_iff.mpr (cover r hr _ ((Finset.mem_filter.mp hs).2.symm.trans eq.symm))

end ThresholdQuarterRetention
