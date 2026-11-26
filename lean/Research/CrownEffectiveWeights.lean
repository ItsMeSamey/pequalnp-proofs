import Research.CrownFutureDiscount

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
namespace EffectiveKraft

def liveSlots {I : Type} [Fintype I] (g : Gate) (w : I → List Bool) : List ℕ :=
  g.inputs.filter (fun a => decide (∃ i, (w i).getD a false = true))

def thinGate {I : Type} [Fintype I] (g : Gate) (w : I → List Bool) : Gate :=
  if isOrGate g then
    match liveSlots g w with
    | [p] => ⟨.and,[p]⟩
    | _ => g
  else g

theorem thin_gate_eval {I : Type} [Fintype I] (g : Gate) (w : I → List Bool) (i : I) :
    gateBool (thinGate g w) (w i) = gateBool g (w i) := by
  unfold thinGate
  split
  next orGate =>
    split
    next p shape =>
      have hor : g.op = .or := by cases h : g.op <;> simp_all [isOrGate]
      have hp : p ∈ g.inputs := by
        apply List.mem_of_mem_filter
        change p ∈ liveSlots g w
        rw [shape];simp
      have unique (a) (am : a ∈ g.inputs) (hot : (w i).getD a false = true) : a=p := by
        have live : a ∈ liveSlots g w := List.mem_filter.mpr ⟨am,decide_eq_true ⟨i,hot⟩⟩
        simpa only [shape,List.mem_singleton] using live
      change GateOp.and.eval _ = _
      apply Bool.eq_iff_iff.mpr
      simp only [gateBool,hor,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
        List.all_nil,id_eq,Bool.and_true,List.any_map,Function.comp_apply,List.any_eq_true]
      constructor
      · intro h; exact ⟨p,hp,h⟩
      · rintro ⟨a,am,hot⟩
        exact unique a am hot ▸ hot
    next => rfl
  next => rfl

def thinGates {I : Type} [Fintype I] : List Gate → (I → List Bool) → List Gate
  | [], _ => []
  | g::gs, w => thinGate g w :: thinGates gs (fun i => advance g (w i))

theorem probe_wires {I : Type} [Fintype I] (gs : List Gate) (w : I → List Bool) (i : I) :
    (Circuit.mk (thinGates gs w) 0).wires (w i) = (Circuit.mk gs 0).wires (w i) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.mk (thinGates gs (fun i => advance g (w i))) 0).wires (advance (thinGate g w) (w i)) = _
    have eq : advance (thinGate g w) (w i) = advance g (w i) := by
      change w i ++ [gateBool (thinGate g w) (w i)] = w i ++ [gateBool g (w i)]
      rw [thin_gate_eval]
    rw [eq]
    exact ih (fun i => advance g (w i))

theorem thin_mono {I : Type} [Fintype I] (gs : List Gate) (w : I → List Bool)
    (hm : Monotone2 (Circuit.mk gs 0)) : Monotone2 (Circuit.mk (thinGates gs w) 0) := by
  induction gs generalizing w with
  | nil => exact hm
  | cons g gs ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl|later
    · unfold thinGate
      split <;> first | exact hm _ (List.mem_cons_self ..) | split <;>
        first | exact hm _ (List.mem_cons_self ..) | exact ⟨Or.inl rfl,by change 1 ≤ 2; decide⟩
    · exact ih (fun i => advance g (w i)) (fun t ht => hm t (List.mem_cons_of_mem _ ht)) k later

theorem thin_or_count_le {I : Type} [Fintype I] (gs : List Gate) (w : I → List Bool) (i : I) :
    (trueOrFlags (thinGates gs w) (w i)).count true ≤ (trueOrFlags gs (w i)).count true := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have eq : advance (thinGate g w) (w i) = advance g (w i) := by
      change w i ++ [gateBool (thinGate g w) (w i)] = w i ++ [gateBool g (w i)]
      rw [thin_gate_eval]
    have gate : isOrGate (thinGate g w) = true → isOrGate g = true := by
      unfold thinGate
      split <;> simp_all
    change ((isOrGate (thinGate g w) && gateBool (thinGate g w) (w i)) ::
        trueOrFlags (thinGates gs (fun i => advance g (w i))) (advance (thinGate g w) (w i))).count true ≤
      ((isOrGate g && gateBool g (w i)) :: trueOrFlags gs (advance g (w i))).count true
    rw [eq,thin_gate_eval]
    simp only [List.count_cons]
    have h := ih (fun i => advance g (w i))
    cases a : isOrGate (thinGate g w) <;> cases b : isOrGate g <;> cases c : gateBool g (w i) <;>
      simp [a,b,c] at * <;> omega

def probes (n : ℕ) : Option (Fin n) → List Bool
  | none => List.replicate n false
  | some i => singleInput i

def circuit (n : ℕ) (C : Circuit) : Circuit := ⟨thinGates C.gates (probes n),C.output⟩

def weight {n : ℕ} (C : Circuit) (r : Fin n) : ℚ := singletonWeight (circuit n C) r

theorem singleton_wires {n} (C : Circuit) (r : Fin n) :
    ((circuit n C).wires (singleInput r)) = C.wires (singleInput r) :=
  probe_wires C.gates (probes n) (some r)

theorem baseline_wires (n : ℕ) (C : Circuit) :
    ((circuit n C).wires (List.replicate n false)) = C.wires (List.replicate n false) :=
  probe_wires C.gates (probes n) none

theorem capacity (n : ℕ) (C : Circuit) (hm : Monotone2 C) (a : ℕ)
    (off : (C.wires (List.replicate n false)).getD a false = false) :
    (∑ i ∈ wireSupport (n:=n) C.gates a, weight C i) ≤ 1 := by
  have sub : wireSupport (n:=n) C.gates a = wireSupport (circuit n C).gates a := by
    ext r
    simp only [wireSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    change (C.wires (singleInput r)).getD a false = true ↔ ((circuit n C).wires (singleInput r)).getD a false = true
    rw [singleton_wires]
  rw [sub]
  exact singleton_weight_capacity (circuit n C) (thin_mono C.gates (probes n) hm) a
    ((baseline_wires n C).symm ▸ off)

end EffectiveKraft
end PEqualNP.Research.MissingCell
