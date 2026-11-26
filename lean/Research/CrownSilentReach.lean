import Research.CrownSilentReachDefs
import Research.CrownSilentCopies
import Research.CrownSingletonQuarter
import Research.CrownSilentIncidence
namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
theorem rawSupport_eq_singleton (C : Circuit) (hm : Monotone2 C) (r : Fin 24)
    (silent : (trueOrFlags C.gates (singleInput r)).count true = 0) (a : ℕ)
    (hot : r ∈ rawSupport C a) (cold : (C.wires (List.replicate 24 false)).getD a false = false) :
    rawSupport C a = {r} := by
  ext t
  constructor
  · intro ht
    have h := silent_cold_is_copy C hm r silent a (Finset.mem_filter.mp hot).2 cold (singleInput t) (by simp [singleInput])
    have b := raw_single_support (Circuit.mk [] 0) r t
    change (singleInput t).getD r.val false = decide (r=t) at b
    exact Finset.mem_singleton.mpr (of_decide_eq_true ((h.trans b).symm.trans (Finset.mem_filter.mp ht).2)).symm
  · intro h
    exact (Finset.mem_singleton.mp h) ▸ hot

theorem rawSupport_le_eight (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 24) (a : ℕ)
    (cold : (C.wires (List.replicate 24 false)).getD a false = false) :
    (rawSupport C a).card ≤ 8 := by
  have pos (t : Fin 24) : (1/8:ℚ) ≤ singletonWeight C t := by
    have h := literal_count_le_diagonal C hm t
    have d := crown_trueOrFlags_le (literalLabel t) C hm rep
    unfold singletonWeight
    generalize (trueOrFlags C.gates (singleInput t)).count true = k at h ⊢
    have : k ≤ 3 := by omega
    interval_cases k <;> norm_num
  have upper : ∑ t ∈ rawSupport C a, singletonWeight C t ≤ 1 := singleton_weight_capacity C hm _ cold
  have low := Finset.sum_le_sum (s := rawSupport C a) (fun t _ => pos t)
  simp only [Finset.sum_const,nsmul_eq_mul] at low
  have cap : ((rawSupport C a).card : ℚ) ≤ 8 := by linarith
  exact_mod_cast cap

def silentReach (C : Circuit) (r : Fin 24) (k : Fin C.gates.length) : Finset (Fin 24) :=
  if r ∈ rawSupport C (operand C k 0) then rawSupport C (operand C k 1) else rawSupport C (operand C k 0)

private theorem hit_reach (C : Circuit) (hm : Monotone2 C) (r q : Fin 24)
    (sil : (trueOrFlags C.gates (singleInput r)).count true = 0) (ne : r≠q)
    (k : Fin C.gates.length) (ok : chargeable C k = true)
    (cross : (r∈rawSupport C (operand C k 0) ∧ q∈rawSupport C (operand C k 1)) ∨
      (r∈rawSupport C (operand C k 1) ∧ q∈rawSupport C (operand C k 0))) :
    silentIncident C r k = true ∧ q ∈ silentReach C r k := by
  rcases cross with ⟨r0,q1⟩ | ⟨r1,q0⟩
  · exact ⟨decide_eq_true (.inl r0),by simpa only [silentReach,ite_eq_left r0] using q1⟩
  · have nr : r ∉ rawSupport C (operand C k 0) := by
      intro hr
      rw [rawSupport_eq_singleton C hm r sil _ hr (chargeable_cold C k ok).1] at q0
      exact ne (Finset.mem_singleton.mp q0).symm
    exact ⟨decide_eq_true (.inr r1),by simpa only [silentReach,ite_eq_right nr] using q0⟩

private theorem reach_cap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 24) (R : Finset (Fin 24))
    (sil : ∀ r∈R, (trueOrFlags C.gates (singleInput r)).count true = 0)
    (r : Fin 24) (k : Fin C.gates.length) (ok : chargeable C k=true) :
    (silentReach C r k).card ≤ if silentBoth C R k then 1 else 8 := by
  have off := chargeable_cold C k ok
  by_cases hb : silentBoth C R k = true
  · rw [ite_eq_left hb]
    obtain ⟨⟨x,hx,h0⟩,⟨y,hy,h1⟩⟩ := of_decide_eq_true hb
    unfold silentReach
    split
    · rw [rawSupport_eq_singleton C hm y (sil _ hy) _ h1 off.2]; simp
    · rw [rawSupport_eq_singleton C hm x (sil _ hx) _ h0 off.1]; simp
  · rw [ite_eq_right hb]
    unfold silentReach
    split
    · exact rawSupport_le_eight C hm rep ors _ off.2
    · exact rawSupport_le_eight C hm rep ors _ off.1

private theorem separate_ports : ∀ i j : Fin 12, rowPort i ≠ colPort j := by decide

private theorem crown_cross_gate (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C) (i j : Fin 12) (ne : i≠j) :
    ∃ k : Fin C.gates.length, chargeable C k = true ∧
      ((rowPort i ∈ rawSupport C (operand C k 0) ∧ colPort j ∈ rawSupport C (operand C k 1)) ∨
       (rowPort i ∈ rawSupport C (operand C k 1) ∧ colPort j ∈ rawSupport C (operand C k 0))) := by
  obtain ⟨k,_,ok,rect⟩ := crown_first_charger C hm rep ne
  refine ⟨k,ok,?_⟩
  simpa only [chargingRect,Finset.mem_union,Finset.mem_product,rowSupport,colSupport,rawSupport,
    Finset.mem_filter,Finset.mem_univ,true_and] using rect

private theorem silent_row_of_cover (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 24) (R : Finset (Fin 24))
    (sil : ∀ r∈R, (trueOrFlags C.gates (singleInput r)).count true = 0)
    (r : Fin 24) (hr : r∈R) (i : Fin 12) (port : Fin 12 ↪ Fin 24)
    (hcover : ∀ j, i≠j → ∃ k, chargeable C k = true ∧
      silentIncident C r k = true ∧ port j ∈ silentReach C r k) :
    11 ≤ 8*((silentGates C R).filter (fun k => silentIncident C r k && !silentBoth C R k)).card +
      ((silentGates C R).filter (fun k => silentIncident C r k && silentBoth C R k)).card := by
  let N := (Finset.univ.erase i).map port
  have num : N.card = 11 := by simp [N,Finset.card_erase_of_mem]
  rw [← num]
  apply silent_neighbor_cover (silentGates C R) N (silentBoth C R) (silentIncident C r) (silentReach C r)
  · intro q hq
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨k,ok,hit,m⟩ := hcover j (Finset.mem_erase.mp hj).1.symm
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok,r,hr,hit⟩,hit,m⟩
  · intro k hk _
    exact reach_cap C hm rep ors R sil r k (Finset.mem_filter.mp hk).2.1

theorem silent_physical_row (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u≠v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 24) (R : Finset (Fin 24))
    (sil : ∀ r∈R, (trueOrFlags C.gates (singleInput r)).count true = 0)
    (r : Fin 24) (hr : r∈R) :
    11 ≤ 8*((silentGates C R).filter (fun k => silentIncident C r k && !silentBoth C R k)).card +
      ((silentGates C R).filter (fun k => silentIncident C r k && silentBoth C R k)).card := by
  revert hr
  refine Fin.addCases (m:=12) (n:=12) (motive := fun r => r ∈ R →
    11 ≤ 8*((silentGates C R).filter (fun k => silentIncident C r k && !silentBoth C R k)).card +
      ((silentGates C R).filter (fun k => silentIncident C r k && silentBoth C R k)).card) ?_ ?_ r
  · intro i hr
    apply silent_row_of_cover C hm rep ors R sil (rowPort i) hr i ⟨colPort,by intro a b h; exact Fin.ext (by simpa [colPort] using congrArg Fin.val h)⟩
    intro j ne
    obtain ⟨k,ok,cross⟩ := crown_cross_gate C hm rep i j ne
    exact ⟨k,ok,hit_reach C hm (rowPort i) (colPort j) (sil _ hr) (separate_ports i j) k ok cross⟩
  · intro i hr
    apply silent_row_of_cover C hm rep ors R sil (colPort i) hr i ⟨rowPort,by intro a b h; exact Fin.ext (congrArg (fun z : Fin 24 => z.val) h)⟩
    intro j ne
    obtain ⟨k,ok,cross⟩ := crown_cross_gate C hm rep j i ne.symm
    refine ⟨k,ok,hit_reach C hm (colPort i) (rowPort j) (sil _ hr) (separate_ports j i).symm k ok ?_⟩
    rcases cross with ⟨a,b⟩|⟨a,b⟩
    · exact .inr ⟨b,a⟩
    · exact .inl ⟨b,a⟩

end PEqualNP.Research.MissingCell
