import LiveIncidenceCapacity
import PEqualNP.Defs.CircuitLowerBounds

namespace ScalarFork.PhysicalLiveIncidence
open PEqualNP.CircuitLowerBounds ScalarFork.LiveIncidence
open scoped BigOperators

def readSlots (g : Gate) : List Nat :=
  match g.op with
  | .and | .or => g.inputs
  | .not => g.inputs.take 1
  | _ => []

abbrev Good (g : Gate) := g.op = .and ∨ g.op = .or ∨ g.op = .not

theorem eval_congr_slots (g : Gate) (hg : Good g) (a b : List Bool)
    (len : a.length = b.length)
    (agree : ∀ i ∈ readSlots g, i < a.length → a.getD i false = b.getD i false) :
    g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
  have same : ∀ i ∈ readSlots g, a.getD i false = b.getD i false := by
    intro i hi
    by_cases h : i < a.length
    · exact agree i hi h
    · rw [List.getD_eq_default a false (by omega : a.length ≤ i),
          List.getD_eq_default b false (by omega : b.length ≤ i)]
  rcases hg with ha | ho | hn
  · have eq : g.inputs.map (fun i => a.getD i false) =
        g.inputs.map (fun i => b.getD i false) :=
      List.map_congr_left (fun i hi => same i (by simpa [readSlots,ha] using hi))
    rw [eq]
  · have eq : g.inputs.map (fun i => a.getD i false) =
        g.inputs.map (fun i => b.getD i false) :=
      List.map_congr_left (fun i hi => same i (by simpa [readSlots,ho] using hi))
    rw [eq]
  · cases e : g.inputs with
    | nil => simp [hn,e,GateOp.eval]
    | cons i is =>
      have he := same i (by simp [readSlots,hn,e])
      simp only [hn,GateOp.eval,List.map_cons,List.headD_cons]
      rw [he]

def gateAt (C : Circuit) (n w : Nat) : Option Gate :=
  if w < n then none else C.gates[w-n]?

def livePins (C : Circuit) (n w : Nat) : List Nat :=
  match gateAt C n w with
  | none => []
  | some g => (readSlots g).filter (fun i => decide (i < w))

theorem pin_lt {C : Circuit} {n w i : Nat} (h : i ∈ livePins C n w) : i < w := by
  unfold livePins at h
  split at h
  · simp at h
  · simpa using (List.mem_filter.mp h).2

inductive Live (C : Circuit) (n : Nat) : Nat → Prop where
  | root : Live C n C.output
  | pin {w i} : Live C n w → i ∈ livePins C n w → Live C n i

theorem live_le_output {C : Circuit} {n i : Nat} (h : Live C n i) : i ≤ C.output := by
  induction h with
  | root => exact Nat.le_refl _
  | pin _ hpin ih => exact (pin_lt hpin).le.trans ih

noncomputable def vertices (C : Circuit) (n : Nat) : Finset Nat := by
  classical
  exact (Finset.range (C.output+1)).filter (Live C n)

@[simp] theorem mem_vertices {C : Circuit} {n i : Nat} :
    i ∈ vertices C n ↔ Live C n i := by
  classical
  simp only [vertices,Finset.mem_filter,Finset.mem_range]
  exact ⟨And.right,fun h => ⟨by have := live_le_output h; omega,h⟩⟩

noncomputable def fanout (C : Circuit) (n i : Nat) : Nat :=
  ∑ w ∈ vertices C n, degree i (livePins C n w)

theorem degree_pos_iff {i : Nat} {ps : List Nat} :
    0 < degree i ps ↔ i ∈ ps := by
  induction ps with
  | nil => simp [degree]
  | cons a ps ih =>
    by_cases h : i = a
    · subst i; simp [degree]
    · simp [degree,h,ih]

theorem live_fanout {C : Circuit} {n i : Nat} (h : Live C n i) (hne : i ≠ C.output) :
    0 < fanout C n i := by
  cases h with
  | root => exact (hne rfl).elim
  | @pin w i hw hi =>
    have le := Finset.single_le_sum (f := fun z => degree i (livePins C n z))
      (fun _ _ => Nat.zero_le _) (mem_vertices.mpr hw)
    exact lt_of_lt_of_le (degree_pos_iff.mpr hi) le

theorem output_fanout (C : Circuit) (n : Nat) : fanout C n C.output = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  by_contra nz
  have hlt := pin_lt (degree_pos_iff.mp (Nat.pos_of_ne_zero nz))
  have hle := live_le_output (mem_vertices.mp hw)
  omega

private theorem degree_sum_over (S : Finset Nat) (ps : List Nat)
    (within : ∀ x ∈ ps, x ∈ S) : (∑ i ∈ S, degree i ps) = ps.length := by
  induction ps with
  | nil => simp [degree]
  | cons a ps ih =>
    have ha := within a (by simp)
    have ht := ih (fun x hx => within x (by simp [hx]))
    simp [degree,Finset.sum_add_distrib,ha,ht,Nat.add_comm]

theorem sum_fanout (C : Circuit) (n : Nat) :
    (∑ i ∈ vertices C n, fanout C n i) =
      ∑ w ∈ vertices C n, (livePins C n w).length := by
  unfold fanout
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  exact degree_sum_over _ _ (fun _ hi => mem_vertices.mpr (.pin (mem_vertices.mp hw) hi))

def sourceCharge (n w : Nat) := if w < n then 1 else 0

def binCharge (C : Circuit) (n w : Nat) : Nat :=
  match gateAt C n w with
  | some g => match g.op with | .and | .or => 1 | _ => 0
  | none => 0

theorem pin_budget (C : Circuit) (n w : Nat)
    (cap : ∀ g, gateAt C n w = some g → g.inputs.length ≤ 2) :
    (livePins C n w).length + sourceCharge n w ≤ 1 + binCharge C n w := by
  by_cases hr : w < n
  · simp [livePins,sourceCharge,binCharge,gateAt,hr]
  · cases h : gateAt C n w with
    | none => simp [livePins,sourceCharge,binCharge,h,hr]
    | some g =>
      have bound := cap g h
      have filt := List.length_filter_le (fun i => decide (i < w)) (readSlots g)
      cases op : g.op <;> simp [livePins,readSlots,sourceCharge,binCharge,h,hr,op] <;>
        simp [readSlots,op] at filt <;> omega

/-- A missing output has one isolated bookkeeping vertex. No source or binary
gate is charged. The normal case counts physical raw wires and occupied forks. -/
theorem physical_capacity (C : Circuit) (n : Nat)
    (cap : ∀ w g, gateAt C n w = some g → g.inputs.length ≤ 2) :
    (∑ w ∈ vertices C n, sourceCharge n w) +
      ((vertices C n).filter (fun i => 2 ≤ fanout C n i)).card ≤
      (∑ w ∈ vertices C n, binCharge C n w) + 1 := by
  classical
  let S := vertices C n
  have ho : C.output ∈ S := mem_vertices.mpr .root
  have localBound (i : Nat) (hi : i ∈ S) :
      (if i = C.output then 0 else 1) + (if 2 ≤ fanout C n i then 1 else 0) ≤
        fanout C n i := by
    by_cases e : i = C.output
    · subst i; simp [output_fanout]
    · have hp := live_fanout (mem_vertices.mp hi) e
      split_ifs <;> omega
  have inc := Finset.sum_le_sum localBound
  have pin := Finset.sum_le_sum (fun w (_ : w ∈ S) => pin_budget C n w (cap w))
  have nonroot : (∑ i ∈ S, (if i = C.output then 0 else 1 : Nat)) + 1 = S.card := by
    rw [← Finset.sum_erase_add S (fun i => if i = C.output then 0 else (1 : Nat)) ho]
    simp only [if_pos rfl,Nat.add_zero]
    have e : (∑ i ∈ S.erase C.output, (if i = C.output then 0 else 1 : Nat)) =
        (S.erase C.output).card := by
      calc
        _ = ∑ _i ∈ S.erase C.output, (1 : Nat) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_neg (Finset.mem_erase.mp hi).1]
        _ = _ := by simp
    rw [e]
    simpa using Finset.card_erase_add_one ho
  simp only [Finset.sum_add_distrib] at inc pin
  have hc : (∑ i ∈ S, (if 2 ≤ fanout C n i then 1 else 0 : Nat)) =
      (S.filter (fun i => 2 ≤ fanout C n i)).card := by
    simpa only [Nat.cast_id] using (Finset.sum_boole (R := Nat) (fun i => 2 ≤ fanout C n i) S)
  have ones : (∑ _i ∈ S, (1 : Nat)) = S.card := by simp
  have flow := sum_fanout C n
  change (∑ i ∈ S, fanout C n i) = ∑ i ∈ S, (livePins C n i).length at flow
  change (∑ i ∈ S, sourceCharge n i) + (S.filter (fun i => 2 ≤ fanout C n i)).card ≤
    (∑ i ∈ S, binCharge C n i) + 1
  rw [hc,flow] at inc
  rw [ones] at pin
  omega

theorem physical_capacity_of_fanin (C : Circuit) (n : Nat)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (∑ w ∈ vertices C n, sourceCharge n w) +
      ((vertices C n).filter (fun i => 2 ≤ fanout C n i)).card ≤
      (∑ w ∈ vertices C n, binCharge C n w) + 1 := by
  apply physical_capacity
  intro w g he
  unfold gateAt at he
  split at he
  · contradiction
  · obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp he
    exact cap g (hg ▸ List.getElem_mem hj)

end ScalarFork.PhysicalLiveIncidence
