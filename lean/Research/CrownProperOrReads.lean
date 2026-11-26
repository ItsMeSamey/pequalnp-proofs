import Research.CrownIndexedOrReads

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def soleOrInput (p : Finset ℕ) (n : ℕ) : ℕ := if h : p.Nonempty then p.min' h else n

def replaceThinOr (g : Gate) (n : ℕ) : Gate :=
  if isOrGate g = true ∧ (orReads g n).card ≤ 1 then ⟨.and,[soleOrInput (orReads g n) n]⟩ else g

def replaceThinOrs : List Gate → ℕ → List Gate
  | [],_ => []
  | g::gs,n => replaceThinOr g n :: replaceThinOrs gs (n+1)

theorem or_value_on_reads (g : Gate) (w : List Bool) (op : isOrGate g = true) :
    gateBool g w = true ↔ ∃ x ∈ orReads g w.length, w.getD x false = true := by
  have og : g.op = .or := by cases h : g.op <;> simp_all [isOrGate]
  simp only [gateBool,og,GateOp.eval,List.any_map,List.any_eq_true,orReads,op,↓reduceIte,
    Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨x,xg,hx⟩
    refine ⟨x,⟨xg,?_⟩,hx⟩
    by_contra! h
    change w.getD x false = true at hx
    rw [getD_missing h] at hx
    contradiction
  · rintro ⟨x,⟨xg,_⟩,hx⟩
    exact ⟨x,xg,hx⟩

private theorem replaceThinOr_eval (g : Gate) (w : List Bool) :
    advance (replaceThinOr g w.length) w = advance g w := by
  by_cases h : isOrGate g = true ∧ (orReads g w.length).card ≤ 1
  · let p := orReads g w.length
    have bound : p.card ≤ 1 := h.2
    have he : gateBool g w = w.getD (soleOrInput p w.length) false := by
      apply Bool.eq_iff_iff.mpr
      rw [or_value_on_reads g w h.1]
      by_cases hp : p.Nonempty
      · have small := Finset.card_le_one.mp bound
        constructor
        · rintro ⟨x,xp,hx⟩
          have eq := small x xp _ (p.min'_mem hp)
          simpa only [soleOrInput,dite_eq_left hp,←eq] using hx
        · intro hv
          exact ⟨soleOrInput p w.length, by simpa only [soleOrInput,dite_eq_left hp] using p.min'_mem hp,hv⟩
      · have empty := Finset.not_nonempty_iff_eq_empty.mp hp
        change (∃ x ∈ p, w.getD x false = true) ↔ _
        simp [empty,soleOrInput]
    change w ++ [gateBool (replaceThinOr g w.length) w] = w ++ [gateBool g w]
    rw [he]
    simp [replaceThinOr,h,gateBool,GateOp.eval,p]
  · simp [replaceThinOr,h]

private theorem replaceThinOrs_eval (gs : List Gate) (w : List Bool) (o : ℕ) :
    (Circuit.mk (replaceThinOrs gs w.length) o).eval w = (Circuit.mk gs o).eval w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.mk (replaceThinOrs gs (w.length+1)) o).eval (advance (replaceThinOr g w.length) w) =
      (Circuit.mk gs o).eval (advance g w)
    rw [replaceThinOr_eval,←advance_len g w]
    exact ih (advance g w)

private theorem replaceThinOrs_len (gs : List Gate) (n : ℕ) :
    (replaceThinOrs gs n).length = gs.length := by
  induction gs generalizing n <;> simp_all [replaceThinOrs]

private theorem replaceThinOrs_mono (gs : List Gate) (n o : ℕ) (hm : Monotone2 ⟨gs,o⟩) :
    Monotone2 ⟨replaceThinOrs gs n,o⟩ := by
  induction gs generalizing n with
  | nil => exact hm
  | cons g gs ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | tail
    · by_cases h : isOrGate g = true ∧ (orReads g n).card ≤ 1
      · simp [replaceThinOr,h]
      · simpa [replaceThinOr,h] using hm g (List.mem_cons_self ..)
    · exact ih (n+1) (fun b hb => hm b (List.mem_cons_of_mem _ hb)) x tail

private theorem replaceThinOrs_count (gs : List Gate) (n : ℕ) :
    ((replaceThinOrs gs n).filter isOrGate).length =
      (orInputSets gs n).countP (fun p => 2 ≤ p.card) := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    by_cases ho : isOrGate g = true
    · have p : orReads g n = g.inputs.toFinset.filter (· < n) := by simp [orReads,ho]
      by_cases small : (orReads g n).card ≤ 1
      · have low : ¬ 2 ≤ (g.inputs.toFinset.filter (· < n)).card := by rw [←p]; omega
        have off : isOrGate ⟨.and,[soleOrInput (orReads g n) n]⟩ = false := rfl
        simp [replaceThinOrs,replaceThinOr,ho,small,off,orInputSets,low,ih]
      · have two : 2 ≤ (g.inputs.toFinset.filter (· < n)).card := by rw [←p]; omega
        simp [replaceThinOrs,replaceThinOr,ho,small,orInputSets,two,ih]
    · simp [replaceThinOrs,replaceThinOr,ho,orInputSets,ih]

theorem crown_or_reads_at_least_two (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    ∀ p ∈ orInputSets C.gates 24, 2 ≤ p.card := by
  let D : Circuit := ⟨replaceThinOrs C.gates 24,C.output⟩
  have dh : Monotone2 D := replaceThinOrs_mono C.gates 24 C.output hm
  have ds : D.size ≤ 40 := by
    change (replaceThinOrs C.gates 24).length ≤ 40
    rw [replaceThinOrs_len]
    exact size
  have dr : Represents (fun u v : Fin 12 => decide (u ≠ v)) D := by
    intro a b
    have eq := replaceThinOrs_eval C.gates (oneEach a b) C.output
    have len : (oneEach a b).length = 24 := by simp [oneEach]
    rw [len] at eq
    exact eq.trans (rep a b)
  have low := crown_size_forty_requires_twenty_three_ors D dh dr ds
  change 23 ≤ ((replaceThinOrs C.gates 24).filter isOrGate).length at low
  rw [replaceThinOrs_count] at low
  have len := orInputSets_length C.gates 24
  have cap := List.countP_le_length (p := fun p : Finset ℕ => decide (2 ≤ p.card))
    (l := orInputSets C.gates 24)
  have eq : (orInputSets C.gates 24).countP (fun p => 2 ≤ p.card) = (orInputSets C.gates 24).length := by omega
  simpa using List.countP_eq_length.mp eq

theorem crown_or_reads_exactly_two (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    ∀ p ∈ orInputSets C.gates 24, p.card = 2 := by
  have ub (gs : List Gate) (n : ℕ) (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      ∀ p ∈ orInputSets gs n, p.card ≤ 2 := by
    induction gs generalizing n with
    | nil => simp [orInputSets]
    | cons g gs ih =>
      have tail := ih (n+1) (fun b hb => fanin b (List.mem_cons_of_mem _ hb))
      intro p hp
      by_cases h : isOrGate g = true
      · rw [orInputSets,ite_eq_left h] at hp
        rcases List.mem_cons.mp hp with rfl | rest
        · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
            ((List.toFinset_card_le _).trans (fanin g (List.mem_cons_self ..)))
        · exact tail p rest
      · exact tail p (by simpa [orInputSets,h] using hp)
  intro p hp
  exact le_antisymm (ub _ _ (fun g hg => (hm g hg).2) p hp)
    (crown_or_reads_at_least_two C hm rep size ors p hp)

end PEqualNP.Research.MissingCell
