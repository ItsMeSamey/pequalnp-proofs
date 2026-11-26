import Research.CrownEffectiveWeights

namespace PEqualNP.Research.MissingCell.EffectiveKraft
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem thin_concat {I : Type} [Fintype I] (pre post : List Gate) (w : I → List Bool) :
    thinGates (pre++post) w = thinGates pre w ++ thinGates post (fun i => (Circuit.mk pre 0).wires (w i)) := by
  induction pre generalizing w with
  | nil => rfl
  | cons g pre ih =>
    change _ :: thinGates (pre++post) (fun i => advance g (w i)) = _ :: _
    rw [ih];rfl

theorem prefix_capacity (n : ℕ) (pre post : List Gate) (hm : Monotone2 (Circuit.mk pre 0))
    (a : ℕ) (cold : ((Circuit.mk pre 0).wires (List.replicate n false)).getD a false = false)
    (B : Finset (Fin n))
    (later : ∀ i ∈ B, 0 < (trueOrFlags
      (thinGates post (fun j => (Circuit.mk pre 0).wires (probes n j)))
      ((Circuit.mk pre 0).wires (singleInput i))).count true) :
    overlapMass (weight (Circuit.mk (pre++post) 0)) (wireSupport (n:=n) pre a) B ≤ 1 := by
  let left := thinGates pre (probes n)
  let right := thinGates post (fun j => (Circuit.mk pre 0).wires (probes n j))
  have ws : wireSupport (n:=n) pre a = wireSupport left a := by
    ext r
    simp only [wireSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [show (Circuit.mk left 0).wires (singleInput r) = (Circuit.mk pre 0).wires (singleInput r) from
      probe_wires pre (probes n) (some r)]
  have zero : (Circuit.mk left 0).wires (List.replicate n false) = (Circuit.mk pre 0).wires (List.replicate n false) :=
    probe_wires pre (probes n) none
  have weights : weight (n:=n) (Circuit.mk (pre++post) 0) = singletonWeight (Circuit.mk (left++right) 0) := by
    change singletonWeight (Circuit.mk (thinGates (pre++post) (probes n)) 0) = _
    rw [thin_concat]
  rw [ws,weights]
  apply future_discount_overlap n left right (thin_mono _ _ hm) a (zero ▸ cold) B
  intro i hi
  rw [show (Circuit.mk left 0).wires (singleInput i) = (Circuit.mk pre 0).wires (singleInput i) from
    probe_wires pre (probes n) (some i)]
  exact later i hi

theorem empty_parent_skipped {I : Type} [Fintype I] (g : Gate) (w : I → List Bool)
    (a b : ℕ) (parents : g.inputs = [a,b]) (dead : ∀ i, (w i).getD a false = false)
    (i : I) : (isOrGate (thinGate g w) && gateBool g (w i)) = false := by
  have absent : ¬∃ j, (w j).getD a false = true := by
    rintro ⟨j,hot⟩
    rw [dead] at hot
    contradiction
  by_cases go : isOrGate g = true
  · have hop : g.op = .or := by cases h : g.op <;> simp_all [isOrGate]
    by_cases hb : ∃ j, (w j).getD b false = true
    · have slots : liveSlots g w = [b] := by
        unfold liveSlots
        rw [parents]
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, absent, hb, ite_false, ite_true]
      simp only [thinGate,go,ite_true,slots]
      rfl
    · have off : (w i).getD b false = false := by
        cases h : (w i).getD b false with
        | false => rfl
        | true => exact False.elim (hb ⟨i,h⟩)
      have gfalse : gateBool g (w i) = false := by
        change g.op.eval (g.inputs.map _) = false
        rw [hop,parents]
        simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,id_eq,List.any_nil,dead,off]
        rfl
      rw [gfalse,Bool.and_false]
  · simp [thinGate,go]

end PEqualNP.Research.MissingCell.EffectiveKraft
