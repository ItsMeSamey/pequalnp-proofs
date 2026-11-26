import Research.CrownMarkerBound

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Research.MissingCell

def gateBool (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def normOrGate (g : Gate) (z : List Bool) : Gate :=
  if isOrGate g && gateBool g z then ⟨.and,[]⟩ else g

def normOrGates : List Gate → List Bool → List Gate
  | [], _ => []
  | g::gs, z => normOrGate g z :: normOrGates gs (advance g z)

private theorem gate_increasing (g : Gate) (z w : List Bool) (hop : g.op = .and ∨ g.op = .or)
    (h : ∀ i, z.getD i false = true → w.getD i false = true) : gateBool g z = true → gateBool g w = true := by
  rcases hop with ha | ho
  · simp only [gateBool,ha,GateOp.eval,List.all_map,List.all_eq_true]
    exact fun hz i hi => h i (hz i hi)
  · simp only [gateBool,ho,GateOp.eval,List.any_map,List.any_eq_true]
    rintro ⟨i,hi,ht⟩
    exact ⟨i,hi,h i ht⟩

private theorem advance_increasing (g : Gate) (z w : List Bool) (hop : g.op = .and ∨ g.op = .or)
    (len : w.length = z.length) (h : ∀ i, z.getD i false = true → w.getD i false = true) :
    ∀ i, (advance g z).getD i false = true → (advance g w).getD i false = true := by
  intro i
  by_cases ht : i < z.length
  · simpa only [getD_advance_lt _ _ _ ht,getD_advance_lt g w i (by omega)] using h i
  · by_cases eq : i = z.length
    · subst i
      rw [getD_advance_eq,←len,getD_advance_eq]
      exact gate_increasing g z w hop h
    · rw [getD_missing (by rw [advance_len];omega : (advance g z).length ≤ i)]
      simp

theorem normOrGates_eval (gs : List Gate) (o : ℕ) (z w : List Bool)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (len : w.length = z.length) (h : ∀ i, z.getD i false = true → w.getD i false = true) :
    (Circuit.mk (normOrGates gs z) o).eval w = (Circuit.mk gs o).eval w := by
  induction gs generalizing z w with
  | nil => rfl
  | cons g gs ih =>
    have hg := hop g (List.mem_cons_self ..)
    have eq : advance (normOrGate g z) w = advance g w := by
      by_cases active : isOrGate g && gateBool g z
      · have on := gate_increasing g z w hg h (Bool.and_eq_true_iff.mp active).2
        change w ++ [gateBool (normOrGate g z) w] = w ++ [gateBool g w]
        rw [on]
        simp only [normOrGate,ite_eq_left active]
        rfl
      · simp [normOrGate,active]
    change (Circuit.mk (normOrGates gs (advance g z)) o).eval (advance (normOrGate g z) w) =
      (Circuit.mk gs o).eval (advance g w)
    rw [eq]
    exact ih (advance g z) (advance g w) (fun a ha => hop a (List.mem_cons_of_mem _ ha))
      (by simp [advance_len,len]) (advance_increasing g z w hg len h)

theorem normOrGates_length (gs : List Gate) (z : List Bool) :
    (normOrGates gs z).length = gs.length := by
  induction gs generalizing z <;> simp_all [normOrGates]

theorem normOrGates_mono (gs : List Gate) (o : ℕ) (z : List Bool) (hm : Monotone2 ⟨gs,o⟩) :
    Monotone2 ⟨normOrGates gs z,o⟩ := by
  induction gs generalizing z with
  | nil => exact hm
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | tail
    · by_cases active : isOrGate g && gateBool g z
      · simp [normOrGate,active]
      · simpa [normOrGate,active] using hm g (List.mem_cons_self ..)
    · exact ih (advance g z) (fun b hb => hm b (List.mem_cons_of_mem _ hb)) a tail

theorem normOrGates_or_count (gs : List Gate) (z : List Bool) :
    ((normOrGates gs z).filter isOrGate).length = falseOrCount gs z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
    have ht := ih (advance g z)
    change (List.filter isOrGate (normOrGate g z :: normOrGates gs (advance g z))).length =
      (if isOrGate g && !gateBool g z then 1 else 0) + falseOrCount gs (advance g z)
    cases ho : isOrGate g <;> cases he : gateBool g z <;>
      simp only [normOrGate,ho,he,Bool.false_and,Bool.true_and,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,↓reduceIte,List.filter_cons,ih,List.length_cons] <;> (try simp [isOrGate]) <;> omega

theorem crown_allzero_no_or (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    (trueOrFlags C.gates (List.replicate 24 false)).count true = 0 := by
  let z := List.replicate 24 false
  let D : Circuit := ⟨normOrGates C.gates z,C.output⟩
  have dh : Monotone2 D := normOrGates_mono C.gates C.output z hm
  have ds : D.size ≤ 40 := by
    change (normOrGates C.gates z).length ≤ 40
    rw [normOrGates_length]
    exact size
  have dr : Represents (fun u v : Fin 12 => decide (u ≠ v)) D := by
    intro u v
    have eq := normOrGates_eval C.gates C.output z (oneEach u v) (fun g hg => (hm g hg).1)
      (by simp [z,oneEach]) (by
        intro i
        have ez (n : ℕ) : (List.replicate n false).getD i false = false := by
          by_cases hi : i<n <;> simp [List.getD_eq_getElem?_getD,hi]
        change (List.replicate 24 false).getD i false = true → _
        rw [ez]
        simp)
    exact eq.trans (rep u v)
  have mino := crown_size_forty_requires_twenty_three_ors D dh dr ds
  change 23 ≤ ((normOrGates C.gates z).filter isOrGate).length at mino
  rw [normOrGates_or_count] at mino
  have b := trueOrFlags_balance C.gates z
  change (trueOrFlags C.gates z).count true = 0
  omega

end CrownDiagonalCharge
