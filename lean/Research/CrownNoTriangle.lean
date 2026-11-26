import Research.CrownTriggerCapacity
import Research.TriggerTriangle

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem crown_no_triangle_collision (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b c : Fin C.gates.length} (ab : a ≠ b) (bc : b ≠ c) (ac : a ≠ c)
    (eab : shareOrRead C a b) (ebc : shareOrRead C b c) (eac : shareOrRead C a c) : False := by
  classical
  let P (j : Fin C.gates.length) := readAt C.gates 24 j.val
  let T := ((P a ∪ P b) ∪ P c) \ ((P a ∩ P b) ∩ P c)
  have bound (j) : (P j).card ≤ 2 := readAt_card_le_two _ _ _ (fun g hg => (hm g hg).2)
  have inter {j k} (edge : shareOrRead C j k) : (P j ∩ P k).Nonempty := by
    obtain ⟨v,hj,hk⟩ := edge
    exact ⟨v,Finset.mem_inter.mpr ⟨hj,hk⟩⟩
  have small : T.card ≤ 3 := CrownCollision.trigger_triangle _ _ _ (bound a) (bound b) (bound c)
    (inter eab) (inter ebc) (by rw [Finset.inter_comm]; exact inter eac)
  have large : 4 ≤ T.card := by
    apply crown_trigger_capacity C hm rep size ors
    intro i k act hk _
    let x := oneEach i i
    let S := activeOrIds C.gates x
    have two : S.card = 2 := (activeOrIds_card ..).trans act
    have cover {j l} (ne : j ≠ l) (edge : shareOrRead C j l) : j ∈ S ∨ l ∈ S := by
      obtain ⟨v,vj,vl⟩ := edge
      by_contra! both
      exact Finset.disjoint_left.mp (crown_inactive_pair_disjoint C hm rep ors i act j l ne both.1 both.2) vj vl
    have pairEq {j l : Fin C.gates.length} (ne : j ≠ l) (hj : j ∈ S) (hl : l ∈ S) :
        S = {j,l} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro m mem
        rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using mem : m = j ∨ m = l) with rfl | rfl <;> assumption
      · simp [ne,two]
    have pairs : S = {a,b} ∨ S = {b,c} ∨ S = {a,c} := by
      rcases cover ab eab with ha | hb
      · rcases cover bc ebc with hb | hc
        · exact .inl (pairEq ab ha hb)
        · exact .inr (.inr (pairEq ac ha hc))
      · rcases cover ac eac with ha | hc
        · exact .inl (pairEq ab ha hb)
        · exact .inr (.inl (pairEq bc hb hc))
    have len : x.length = 24 := by simp [x,oneEach]
    have gate (j : Fin C.gates.length) : j ∈ S ↔ ∃ v ∈ P j, (C.wires x).getD v false = true := by
      simpa only [P,S,← len,Circuit.wires] using activeOrIds_iff_final_parent C.gates x j
    obtain ⟨v,vr,on⟩ := (gate k).mp hk
    refine ⟨v,Finset.mem_sdiff.mpr ⟨?_,?_⟩,vr,on⟩
    · change k ∈ S at hk
      have location : k = a ∨ k = b ∨ k = c := by
        rcases pairs with h|h|h <;> rw [h] at hk <;>
          simp only [Finset.mem_insert,Finset.mem_singleton] at hk <;> tauto
      rcases location with rfl|rfl|rfl <;> simp only [Finset.mem_union] <;> tauto
    · intro hv
      obtain ⟨hab,hc⟩ := Finset.mem_inter.mp hv
      obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hab
      have yesA := (gate a).mpr ⟨v,ha,on⟩
      have yesB := (gate b).mpr ⟨v,hb,on⟩
      have yesC := (gate c).mpr ⟨v,hc,on⟩
      rcases pairs with h|h|h
      · simp [h,Ne.symm ac,Ne.symm bc] at yesC
      · simp [h,ab,ac] at yesA
      · simp [h,Ne.symm ab,bc] at yesB
  omega
end PEqualNP.Research.MissingCell
