import Research.CrownMixedGate
import Research.CrownChargeWeights
import Research.CrownSingletonKraft

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

abbrev rowPort (i : Fin 12) : Fin 24 := Fin.castAdd 12 i
abbrev colPort (j : Fin 12) : Fin 24 := Fin.natAdd 12 j

private theorem pair_reads_finite : ∀ (i j : Fin 12) (p : Fin 24),
    (oneEach i j).getD p.val false =
      ((singleInput (rowPort i)).getD p.val false || (singleInput (colPort j)).getD p.val false) := by
  decide

theorem pair_reads (i j : Fin 12) (p : ℕ) : (oneEach i j).getD p false =
      ((singleInput (rowPort i)).getD p false || (singleInput (colPort j)).getD p false) := by
  by_cases h : p<24
  · exact pair_reads_finite i j ⟨p,h⟩
  · rw [getD_missing (by simp [oneEach];omega : (oneEach i j).length ≤ p),
      getD_missing (by simp [singleInput];omega : (singleInput (rowPort i)).length ≤ p),
      getD_missing (by simp [singleInput];omega : (singleInput (colPort j)).length ≤ p)]
    rfl

private theorem crown_singles_off (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (u : Fin 12) :
    C.eval (singleInput (rowPort u)) = false ∧ C.eval (singleInput (colPort u)) = false := by
  have diag := rep u u
  simp only [ne_eq,not_true_eq_false,decide_false] at diag
  constructor
  · cases h : C.eval (singleInput (rowPort u)) with
    | false => rfl
    | true =>
      have y := eval_mono_live C 24 _ (oneEach u u) hm (by simp [singleInput]) (by simp [oneEach])
        (fun p _ hp => by rw [pair_reads, hp]; rfl) h
      rw [diag] at y
      contradiction
  · cases h : C.eval (singleInput (colPort u)) with
    | false => rfl
    | true =>
      have y := eval_mono_live C 24 _ (oneEach u u) hm (by simp [singleInput]) (by simp [oneEach])
        (fun p _ hp => by rw [pair_reads,hp]; exact Bool.or_true _) h
      rw [diag] at y
      contradiction

private theorem zero_wire_off (C : Circuit) (hm : Monotone2 C) (a : ℕ) (t : Fin 24)
    (off : (C.wires (singleInput t)).getD a false = false) :
    (C.wires (List.replicate 24 false)).getD a false = false := by
  let D := Circuit.mk C.gates a
  have hD : Monotone2 D := hm
  cases hz : (C.wires (List.replicate 24 false)).getD a false with
  | false => rfl
  | true =>
    have h := eval_mono_live D 24 (List.replicate 24 false) (singleInput t) hD (by simp) (by simp [singleInput])
      (fun p _ hp => by have zero (n : ℕ) : (List.replicate n false).getD p false = false := by
                          simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate]; split <;> rfl
                        rw [zero] at hp; contradiction) hz
    change (C.wires (singleInput t)).getD a false = true at h
    rw [off] at h
    contradiction

def operand (C : Circuit) (k : Fin C.gates.length) (s : ℕ) : ℕ := C.gates[k].inputs.getD s 0

def chargeable (C : Circuit) (k : Fin C.gates.length) : Bool :=
  let activeAnd := match C.gates[k].op with | .and => true | _ => false
  activeAnd && decide (C.gates[k].inputs.length = 2) &&
    !(C.wires (List.replicate 24 false)).getD (operand C k 0) false &&
    !(C.wires (List.replicate 24 false)).getD (operand C k 1) false

def rowSupport (C : Circuit) (p : ℕ) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => (C.wires (singleInput (rowPort i))).getD p false)
def colSupport (C : Circuit) (p : ℕ) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => (C.wires (singleInput (colPort i))).getD p false)

def chargingRect (C : Circuit) (k : Fin C.gates.length) : Finset (Fin 12 × Fin 12) :=
  let a := operand C k 0
  let b := operand C k 1
  (rowSupport C a ×ˢ colSupport C b) ∪ (rowSupport C b ×ˢ colSupport C a)

theorem crown_first_charger (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) {i j : Fin 12} (ne : i≠j) :
    ∃ k : Fin C.gates.length, firstMixed C.gates (oneEach i j)
      (singleInput (rowPort i)) (singleInput (colPort j)) k.val ∧
      chargeable C k = true ∧ (i,j) ∈ chargingRect C k := by
  obtain ⟨k,first,a,b,hand,hab,_,_,either⟩ := first_mixed_and C (oneEach i j)
    (singleInput (rowPort i)) (singleInput (colPort j)) hm
    (by simp [singleInput,oneEach]) (by simp [singleInput,oneEach])
    (fun p hp => Bool.or_eq_true_iff.mp ((pair_reads i j p).symm.trans hp))
    ((rep i j).trans (decide_eq_true ne))
    (crown_singles_off C hm rep i).1 (crown_singles_off C hm rep j).2
  have ea : operand C k 0 = a := by unfold operand; rw [hab]; rfl
  have eb : operand C k 1 = b := by unfold operand; rw [hab]; rfl
  refine ⟨k,first,?_⟩
  rcases either with ⟨ar,ac,br,bc⟩ | ⟨br,bc,ar,ac⟩
  · have aoff := zero_wire_off C hm a (colPort j) ac
    have boff := zero_wire_off C hm b (rowPort i) br
    constructor
    · unfold chargeable; rw [hand,hab,ea,eb,aoff,boff]; rfl
    · apply Finset.mem_union_left
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,ea ▸ ar⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,eb ▸ bc⟩⟩
  · have aoff := zero_wire_off C hm a (rowPort i) ar
    have boff := zero_wire_off C hm b (colPort j) bc
    constructor
    · unfold chargeable; rw [hand,hab,ea,eb,aoff,boff]; rfl
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,eb ▸ br⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,ea ▸ ac⟩⟩

def singletonMass (C : Circuit) (a : ℕ) : ℚ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin 24 => (C.wires (singleInput t)).getD a false), singletonWeight C t

theorem singletonMass_split (C : Circuit) (a : ℕ) : singletonMass C a =
    (∑ u ∈ rowSupport C a, singletonWeight C (rowPort u)) +
      ∑ v ∈ colSupport C a, singletonWeight C (colPort v) := by
  simp only [singletonMass,rowSupport,colSupport,Finset.sum_filter]
  exact Fin.sum_univ_add (a := 12) (b := 12) _

theorem crown_weighted_edge_charge (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2),
      singletonWeight C (rowPort p.1) * singletonWeight C (colPort p.2) ≤
    ∑ k ∈ Finset.univ.filter (fun k => chargeable C k = true),
      singletonMass C (operand C k 0) * singletonMass C (operand C k 1) := by
  have pos (t : Fin 24) : 0 ≤ singletonWeight C t := by unfold singletonWeight; positivity
  let r (i : Fin 12) := singletonWeight C (rowPort i)
  let c (j : Fin 12) := singletonWeight C (colPort j)
  apply le_trans (CrownCharge.sum_cover _ _ (chargingRect C) (fun p => r p.1*c p.2)
    (fun p => mul_nonneg (pos _) (pos _)) ?_)
  · apply Finset.sum_le_sum
    intro k _
    rw [singletonMass_split,singletonMass_split]
    exact CrownCharge.crossed_rectangle_bound _ _ _ _ r c (fun _ => pos _) (fun _ => pos _)
  · intro p hp
    obtain ⟨k,_,good,hit⟩ := crown_first_charger C hm rep (Finset.mem_filter.mp hp).2
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,good⟩,hit⟩

end PEqualNP.Research.MissingCell
