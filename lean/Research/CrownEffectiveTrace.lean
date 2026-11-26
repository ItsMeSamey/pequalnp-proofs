import Research.CrownEffectiveWeights

namespace PEqualNP.Research.MissingCell.EffectiveKraft
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def activeFlag {I : Type} [Fintype I] (g : Gate) (w : I → List Bool) (i : I) : Bool :=
  isOrGate g && gateBool g (w i) && decide (2 ≤ (liveSlots g w).length)

theorem flag_exact {I : Type} [Fintype I] (g : Gate) (w : I → List Bool) (i : I) :
    (isOrGate (thinGate g w) && gateBool (thinGate g w) (w i)) = activeFlag g w i := by
  rw [thin_gate_eval]
  by_cases go : isOrGate g = true
  · have hor : g.op = .or := by cases eq : g.op <;> simp_all [isOrGate]
    cases slots : liveSlots g w with
    | nil =>
      have off : gateBool g (w i) = false := by
        cases h : gateBool g (w i) with
        | false => rfl
        | true =>
          obtain ⟨a,am,hot⟩ : ∃ a ∈ g.inputs, (w i).getD a false = true := by
            simpa [gateBool,hor,GateOp.eval] using h
          have present : a ∈ liveSlots g w := List.mem_filter.mpr ⟨am,decide_eq_true ⟨i,hot⟩⟩
          simp [slots] at present
      simp [activeFlag,off]
    | cons a as =>
      cases as with
      | nil => simp only [thinGate,go,slots,ite_true,activeFlag]
               cases gateBool g (w i) <;> rfl
      | cons b bs => simp [thinGate,go,slots,activeFlag]
  · simp [thinGate,go,activeFlag]

def activeFlags {I : Type} [Fintype I] : List Gate → (I → List Bool) → I → List Bool
  | [], _, _ => []
  | g::gs,w,i => activeFlag g w i :: activeFlags gs (fun j => advance g (w j)) i

theorem trace_exact {I : Type} [Fintype I] (gs : List Gate) (w : I → List Bool) (i : I) :
    trueOrFlags (thinGates gs w) (w i) = activeFlags gs w i := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (isOrGate (thinGate g w) && gateBool (thinGate g w) (w i)) :: _ = activeFlag g w i :: _
    rw [flag_exact]
    congr 1
    have vals : advance (thinGate g w) (w i) = advance g (w i) := by
      change w i ++ [gateBool (thinGate g w) (w i)] = w i ++ [gateBool g (w i)]
      rw [thin_gate_eval]
    rw [vals]
    exact ih _

theorem weight_eq {n : ℕ} (C : Circuit) (i : Fin n) :
    weight C i = (1/2:ℚ) ^ (activeFlags C.gates (probes n) (some i)).count true := by
  unfold weight singletonWeight circuit
  change (1/2:ℚ) ^ (trueOrFlags (thinGates C.gates (probes n)) ((probes n) (some i))).count true = _
  rw [trace_exact]
theorem activeFlags_append {I : Type} [Fintype I] (pre post : List Gate)
    (w : I → List Bool) (i : I) :
    activeFlags (pre ++ post) w i =
      activeFlags pre w i ++ activeFlags post (fun j => (Circuit.mk pre 0).wires (w j)) i := by
  induction pre generalizing w with
  | nil => rfl
  | cons g pre ih =>
    change _ :: activeFlags (pre ++ post) (fun j => advance g (w j)) i = _ :: _
    rw [ih]
    rfl

theorem physical_prefix_factor {n : ℕ} (pre post : List Gate) (i : Fin n) :
    weight (Circuit.mk (pre ++ post) 0) i =
      weight (Circuit.mk pre 0) i *
        (1/2:ℚ) ^ (activeFlags post (fun j => (Circuit.mk pre 0).wires (probes n j)) (some i)).count true := by
  rw [weight_eq,weight_eq]
  change (1/2:ℚ) ^ (activeFlags (pre ++ post) (probes n) (some i)).count true = _
  rw [activeFlags_append,List.count_append,pow_add]

end PEqualNP.Research.MissingCell.EffectiveKraft
