import ThresholdLeakPins
import ThresholdFlowFanout
namespace ThresholdOccurrenceDebit
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdSharedFlow ThresholdLeakPins
open scoped BigOperators
variable {C : Circuit} {n : Nat} (L : Layout C n)
def incoming (p : Pin C → Bool) (i : Id C) := (p (i,false)).toNat+(p (i,true)).toNat
def rawFixed (p : Pin C → Bool) :=
  (Finset.univ.filter (fun s : Pin C => source L s<n ∧ p s=true)).card
def kept (p : Pin C → Bool) (r : Id C → Bool) (i : Id C) : Nat :=
  if r i || p (i,false) || p (i,true) then 0 else 1

private theorem pin_conservation (p : Pin C → Bool) (r : Id C → Bool)
    (link : ∀ q a, source L q=n+a.val → p q=r a) (q : Pin C) :
    (p q).toNat = (if source L q<n then (p q).toNat else 0)+
      ∑ a : Id C, if r a then (decide (source L q=n+a.val)).toNat else 0 := by
  classical
  have earlier : source L q<n+C.gates.length := by
    have hl := (L.atIndex q.1).leftEarlier
    have hr := (L.atIndex q.1).rightEarlier
    have small := q.1.isLt
    unfold source; split <;> omega
  by_cases raw : source L q<n
  · have ne (a : Id C) : source L q≠n+a.val := by omega
    simp [raw,ne]
  · let a : Id C := ⟨source L q-n,by omega⟩
    have eq : source L q=n+a.val := by dsimp [a]; omega
    have test (b : Id C) : (source L q=n+b.val) ↔ b=a := by
      rw [eq]; constructor
      · intro hh; apply Fin.ext; omega
      · rintro rfl; rfl
    rw [Finset.sum_eq_single a]
    · rw [link q a eq]
      cases h : r a <;> simp [raw,h,eq]
    · intro b _ ne; simp [test,ne]
    · simp

theorem conservation (p : Pin C → Bool) (r : Id C → Bool)
    (link : ∀ q a, source L q=n+a.val → p q=r a) :
    (∑ i : Id C,incoming p i) = rawFixed L p+∑ a : Id C, if r a then fan L a else 0 := by
  classical
  have pinSplit (q : Pin C) :
      (p q).toNat = (if source L q<n ∧ p q=true then 1 else 0)+
      ∑ a : Id C, if r a then (decide (source L q=n+a.val)).toNat else 0 := by
    have h := pin_conservation L p r link q
    by_cases raw : source L q<n <;> cases v : p q <;> simpa [raw,v] using h
  have all := Finset.sum_congr (s₁:=Finset.univ) rfl (fun q _ => pinSplit q)
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)] at all
  have columns (a : Id C) :
      (∑ q : Pin C,if r a then (decide (source L q=n+a.val)).toNat else 0)=
        (if r a then fan L a else 0) := by
    cases h : r a <;> simp [h,fan,slots,source,Fintype.sum_prod_type,Fintype.sum_bool,Nat.add_comm]
  simp only [columns,Finset.sum_boole,Nat.cast_id] at all
  simpa only [rawFixed,incoming,Fintype.sum_prod_type,Fintype.sum_bool,Nat.add_comm] using all

/-- Each constant shared producer has an additional unit of credit after
two constant input pins are paid. The observer must be nonconstant. -/
theorem telescope (p : Pin C → Bool) (r : Id C → Bool) (H : Finset (Id C))
    (link : ∀ q a, source L q=n+a.val → p q=r a)
    (both : ∀ i, p (i,false)=true → p (i,true)=true → r i=true)
    (live : ∀ i, r i=true → 1≤fan L i)
    (shared : ∀ i∈H, r i=true ∧ 2≤fan L i) :
    (∑ i : Id C,kept p r i)+rawFixed L p+H.card≤C.gates.length := by
  classical
  have row (i : Id C) : kept p r i+incoming p i+(if i∈H then 1 else 0)≤
      1+(if r i then fan L i else 0) := by
    by_cases hi : i∈H
    · obtain ⟨out,paid⟩ := shared i hi
      cases a : p (i,false) <;> cases b : p (i,true) <;>
        simp [hi,out,kept,incoming,a,b] <;> omega
    · cases h : r i with
      | true =>
        have paid := live i h
        cases a : p (i,false) <;> cases b : p (i,true) <;>
          simp [hi,h,kept,incoming,a,b] <;> omega
      | false =>
        have impossible : ¬(p (i,false)=true ∧ p (i,true)=true) := fun z => by
          have off := both i z.1 z.2; simp [h] at off
        cases a : p (i,false) <;> cases b : p (i,true) <;>
          simp_all [kept,incoming]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => row i)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,Nat.cast_id] at h
  have exactPins := conservation L p r link
  omega
#print axioms telescope
end ThresholdOccurrenceDebit
