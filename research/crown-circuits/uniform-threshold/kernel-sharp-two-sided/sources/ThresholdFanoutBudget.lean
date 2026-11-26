import ThresholdRegularSource
import T2MinimalLive
open PEqualNP.CircuitLowerBounds
namespace ThresholdFanoutBudget
open T2OrPartition

/-- A stopped, nonoutput OR with exactly one later operand occurrence feeds a non-OR. -/
theorem singleton_target {C : Circuit} {n : Nat} {i j : Id C}
    (stop : T2OrPartition.next C n i = none)
    (root : isOr C i = true) (nonout : C.output ≠ n+i.val)
    (one : readers C (n+i.val) = [j]) (later : i < j) : isOr C j = false := by
  cases hj : isOr C j with
  | false => rfl
  | true => simp [T2OrPartition.next, one, root, hj, nonout, later] at stop

/-- Each live gate can pay one mandatory pin. A gate of fanout at least two
pays one additional pin. The possible output exception carries unit slack. -/
theorem mandatory_and_shared {α : Type} (rows : List α) (f : α → Nat)
    (out : α → Bool) (live : ∀ i ∈ rows, out i = false → 1 ≤ f i) :
    rows.length + (rows.filter (fun i => decide (2 ≤ f i))).length ≤
      (rows.map f).sum + (rows.filter out).length := by
  let shared := fun i => decide (2 ≤ f i)
  change rows.length + (rows.filter shared).length ≤ _
  induction rows with
  | nil => simp
  | cons i rows ih =>
    have tail := ih (fun j hj => live j (by simp [hj]))
    have paid := live i (by simp)
    have strong : shared i=true → 2 ≤ f i := by simp [shared]
    cases ho : out i <;> cases hs : shared i <;>
      simp only [List.filter_cons,ho,hs,Bool.false_eq_true,ite_false,ite_true,
        List.length_cons,List.map_cons,List.sum_cons] <;>
      first | exact (by have h := paid ho; have h' := strong hs; omega)
            | exact (by have h := paid ho; omega)
            | exact (by have h := strong hs; omega)
            | omega

/-- Count actual AND input occurrences by recording the wire IDs on both
ports. Repetitions in the port list are allowed; the charged roots are distinct. -/
theorem root_partition (roots : List Nat) (unique : roots.Nodup)
    (andPorts : List Nat) (out : Nat) (shared : List Nat)
    (classify : ∀ w ∈ roots, w ∈ andPorts ∨ w = out ∨ w ∈ shared) :
    roots.length ≤ andPorts.length + 1 + shared.length := by
  classical
  let available := andPorts ++ [out] ++ shared
  have sub : roots.toFinset ⊆ available.toFinset := by
    intro w hw
    have mem := classify w (List.mem_toFinset.mp hw)
    rcases mem with port | eq | branched <;> simp_all [available]
  have bound := Finset.card_le_card sub
  have upper := List.toFinset_card_le available
  rw [List.toFinset_card_of_nodup unique] at bound
  exact (bound.trans upper).trans_eq (by simp [available,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])

/-- The additive form permits negative surplus: only g+2 occurs on the right
of the final physical budget, with 2n retained on the left. -/
theorem physical_budget (C : Circuit) (n a v : Nat)
    (fan : Id C → Nat) (output : Id C → Bool)
    (live : ∀ i ∈ List.finRange C.gates.length, output i = false → 1 ≤ fan i)
    (uniqueOutput : ((List.finRange C.gates.length).filter output).length ≤ 1)
    (balance : ((List.finRange C.gates.length).map fan).sum + 2*n =
      2*C.gates.length)
    (rootCharge : v ≤ 2*a+1+
      ((List.finRange C.gates.length).filter (fun i => decide (2 ≤ fan i))).length) :
    v + 2*n ≤ 2*a + C.gates.length + 2 := by
  have h := mandatory_and_shared (List.finRange C.gates.length) fan output live
  simp only [List.length_finRange] at h
  let z := ((List.finRange C.gates.length).filter (fun i => decide (2 ≤ fan i))).length
  change C.gates.length + z ≤ _ at h
  change v ≤ 2*a+1+z at rootCharge
  omega

/-- Concrete forest vertex list and physical fanout. The remaining antecedents
are the live-gate, double-counting and root-classification bridges. -/
theorem forest_budget {C : Circuit} {n a : Nat} (L : ThresholdOrExtraction.Layout C n)
    (andPorts : List Nat) (price : andPorts.length ≤ 2*a)
    :
    let ids := List.finRange C.gates.length
    let fan := fun i : Id C => (readers C (n+i.val)).length
    let output := fun i : Id C => decide (C.output = n+i.val)
    let bs := ThresholdOrExtraction.batchVertices (ThresholdOrExtraction.forest L Fin.val)
    ∀ (unique : (bs.map ThresholdOrGroups.Block.out).Nodup)
    (live : ∀ i ∈ ids, output i = false → 1 ≤ fan i)
    (one : (ids.filter output).length ≤ 1)
    (balance : (ids.map fan).sum + 2*n = 2*C.gates.length)
    (classify : ∀ w ∈ bs.map ThresholdOrGroups.Block.out, w ∈ andPorts ∨ w = C.output ∨
      w ∈ (ids.filter (fun i => decide (2 ≤ fan i))).map (fun i => n+i.val)),
    bs.length + 2*n ≤ 2*a+C.gates.length+2 := by
  intro ids fan output bs unique live one balance classify
  have h := root_partition _ unique andPorts C.output _ classify
  simp only [List.length_map] at h
  apply physical_budget C n a bs.length fan output live one balance
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right price 1) _)

open ThresholdOrExtraction ThresholdOrGroups T2SoleOrSplice

theorem balance_slots {C : Circuit} {n : Nat} (L : Layout C n)
    (twice : ∀ w<n, (readers C w).length=2) :
    ((List.finRange C.gates.length).map (fun i => (readers C (n+i.val)).length)).sum +
      2*n = 2*C.gates.length := by
  let ids := List.finRange C.gates.length
  have scan (k : Nat) : ((List.finRange k).map (fun i => (readers C (n+i.val)).length)).sum +
      2*n = (ids.map (earlyPorts C (n+k))).sum := by
    induction k with
    | zero => simpa [ids] using (regular_total C n twice).symm
    | succ k ih =>
      rw [List.finRange_succ_last, List.map_append, List.sum_append]
      have step := list_charge C (n+k) ids
      change _ = _ + (readers C (n+k)).length at step
      rw [←Nat.add_assoc n k 1]
      simp [List.map_map,Function.comp_def] at *
      omega
  have full (i : Id C) : earlyPorts C (n+C.gates.length) i=2 := by
    have gate := L.atIndex i
    have hl := gate.leftEarlier
    have hr := gate.rightEarlier
    have hi := i.isLt
    have xl : L.left i < n+C.gates.length := by omega
    have xr : L.right i < n+C.gates.length := by omega
    unfold earlyPorts
    rw [layout_inputs gate]
    simp [List.countP_cons,xl,xr]
  have total (xs : List (Id C)) : (xs.map (earlyPorts C (n+C.gates.length))).sum =
      2*xs.length := by
    induction xs with
    | nil => simp
    | cons i xs ih => simp [full,ih]; omega
  exact (scan _).trans (by simpa [ids] using total ids)

theorem live_slots {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
    (i : Id C) (nonout : C.output ≠ n+i.val) : 1 ≤ (readers C (n+i.val)).length := by
  have g := L.atIndex i
  obtain ⟨pre,post,hg,hp⟩ := g.layout
  have eqC : C = ⟨pre ++ ResidualSurplus.binary (L.op i) (L.left i) (L.right i) :: post,
    C.output⟩ := by cases C; simp_all
  have m := T2MinimalLive.consumer_at_minimum n (L.left i) C.output pre post
    (ResidualSurplus.binary (L.op i) (L.left i) (L.right i)) (eqC ▸ M)
    (hp ▸ g.leftEarlier) (hp ▸ nonout)
  obtain ⟨reader,mem,slot⟩ := m
  have actual : reader ∈ C.gates := by rw [hg]; simp [mem]
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp actual
  have physical : n+i.val ∈ (C.gates.get ⟨j,hj⟩).inputs := by simpa [ej,hp] using slot
  have hit := read_mem physical
  exact List.length_pos_of_mem hit

theorem output_unique (C : Circuit) (n : Nat) :
    ((List.finRange C.gates.length).filter (fun i => decide (C.output=n+i.val))).length ≤ 1 := by
  let xs := (List.finRange C.gates.length).filter (fun i => decide (C.output=n+i.val))
  have ord : xs.Pairwise (· < ·) := (List.pairwise_lt_finRange C.gates.length).filter _
  have equal (i : Id C) (hi : i∈xs) : C.output=n+i.val := by simpa [xs] using (List.mem_filter.mp hi).2
  change xs.length ≤ 1
  cases hx : xs with
  | nil => simp
  | cons i tail =>
    cases ht : tail with
    | nil => simp
    | cons j rest =>
      have hi := equal i (by simp [hx])
      have hj := equal j (by simp [hx,ht])
      rw [hx,ht] at ord
      have lt := (List.pairwise_cons.mp ord).1 j (by simp)
      change i.val < j.val at lt
      omega

theorem unique_batch {C : Circuit} {n : Nat} (L : Layout C n) :
    ((batchVertices (forest L Fin.val)).map Block.out).Nodup := by
  have sorted := (forest_ordered L Fin.val).filter (fun b => b.batch==1)
  change ((batchVertices (forest L Fin.val)).map Block.out).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  exact sorted.imp (fun h => ne_of_lt h)

def andIds (C : Circuit) := (List.finRange C.gates.length).filter (fun i => !(T2OrPartition.isOr C i))
def andPins (C : Circuit) := (andIds C).flatMap (fun i => (C.gates.get i).inputs)

theorem and_pin_count {C : Circuit} {n : Nat} (L : Layout C n) :
    (andPins C).length = 2*(andIds C).length := by
  have count (xs : List (Id C)) : (xs.flatMap (fun i => (C.gates.get i).inputs)).length =
      2*xs.length := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.flatMap_cons,List.length_append,layout_inputs (L.atIndex i),ih,List.length_cons,
        List.length_nil]
      omega
  exact count _

theorem reader_pin {C : Circuit} {w : Nat} {j : Id C} (mem : j ∈ readers C w) :
    w ∈ (C.gates.get j).inputs := by
  obtain ⟨i,_,hit⟩ := List.mem_flatMap.mp mem
  obtain ⟨slot,hs,eq⟩ := List.mem_map.mp hit
  change i=j at eq
  subst i
  have equal : slot=w := by simpa using (List.mem_filter.mp hs).2
  exact equal ▸ (List.mem_filter.mp hs).1

theorem classify_batch {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
    (w : Nat) (hit : w ∈ (batchVertices (forest L Fin.val)).map Block.out) :
    w ∈ andPins C ∨ w=C.output ∨ w ∈ ((List.finRange C.gates.length).filter
      (fun i => decide (2 ≤ (readers C (n+i.val)).length))).map (fun i => n+i.val) := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hit
  obtain ⟨hforest,batch⟩ := List.mem_filter.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hforest
  rw [makeBlock_out]
  have stop : T2OrPartition.next C n i=none := by
    simpa using (List.mem_filter.mp hi).2
  have root : T2OrPartition.isOr C i=true := by
    apply (physical_op L i).mpr
    cases e : L.op i with
    | or => rfl
    | and =>
      have zero : (makeBlock L Fin.val i).batch=0 := by
        unfold makeBlock
        split <;> simp_all [Block.batch]
      simp [zero] at batch
  by_cases obs : C.output=n+i.val
  · exact Or.inr (Or.inl obs.symm)
  by_cases shared : 2 ≤ (readers C (n+i.val)).length
  · exact Or.inr (Or.inr (List.mem_map.mpr ⟨i,by simp [shared],rfl⟩))
  have live := live_slots L M i obs
  obtain ⟨j,one⟩ : ∃ j, readers C (n+i.val)=[j] := by
    cases e : readers C (n+i.val) with
    | nil => simp [e] at live
    | cons j tail =>
      cases h : tail with
      | nil => exact ⟨j,rfl⟩
      | cons k ks => simp [e,h] at shared
  have pin := reader_pin (C := C) (w := n+i.val) (j := j) (by simp [one])
  have gate := L.atIndex j
  have lt : i<j := by
    rw [layout_inputs gate] at pin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at pin
    have hl := gate.leftEarlier
    have hr := gate.rightEarlier
    change i.val < j.val
    rcases pin with h|h <;> omega
  have andGate := singleton_target stop root obs one lt
  exact Or.inl (List.mem_flatMap.mpr ⟨j,by simp [andIds,andGate],pin⟩)

open T2CubeDeletion T2RegularOrDelete ResidualSurplus in
theorem regular_vertex_budget {n out : Nat} {gs : List Raw}
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := ThresholdRegularSource.layout n gs out M.eligible
    (batchVertices (forest L Fin.val)).length + 2*n ≤ 2*(andIds C).length+C.gates.length+2 := by
  intro C L
  have twice := (ThresholdRegularSource.regular_inputs n gs out M.eligible reg).2.1
  apply forest_budget L (andPins C) (Nat.le_of_eq (and_pin_count L))
  · exact unique_batch L
  · intro i _ h
    exact live_slots L M i (by simpa using h)
  · exact output_unique C n
  · exact balance_slots L twice
  · exact classify_batch L M

#print axioms regular_vertex_budget
end ThresholdFanoutBudget
