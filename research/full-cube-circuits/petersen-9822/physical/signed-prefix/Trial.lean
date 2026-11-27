import Prefix8
namespace Research.Signed9822
open PEqualNP.Outside.L_meta_9825.Engine
open PEqualNP.CircuitLowerBounds
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffffffffffffffffffffffffffffffffffffffffffffffffffeaeaffffc0c0fffffffffffffffffffffffffffafff0ffffffffffffffffffffffffffeaffc0fffffffffffefcfcfffffffffffaf0f0ffeeeeeeffeeccccffeaeaeaffeac0c0
def predicate (x : Fin 10 → Bool) : Bool :=
  (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem onRows : ∀ r : Row, bit r target = predicate (sample r) := by decide +kernel
theorem targetProper : proper target := by unfold proper; decide +kernel
theorem liftAtThree (prior : Lower true (varsX 1015) (graphGoal 1015) 14) :
    Lower true inputs target 15 := by
  let witnesses := graphPairs 8 (4 <<< 12)
  have chk : checkLift (fixRows 8 0) target inputs (varsX 1015) (graphGoal 1015) witnesses = true := by
    decide +kernel
  have h := lift_ok chk targetProper (proper_of _ (by decide +kernel)) prior
  have card : (witnesses.map Prod.fst).toFinset.card = 1 := by decide +kernel
  simpa only [card] using h
theorem binaryFloorOfFace (prior : Lower true (varsX 1015) (graphGoal 1015) 14)
    (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = predicate x) :
    15 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have eq : (execute C.gates inputs).getD C.output zero = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C hf C.output r).trans ((hc (sample r)).trans (onRows r).symm)
  have out := get_rep (u:=true) (execute C.gates inputs) C.output
  rw [eq] at out
  unfold PEqualNP.Outside.L_meta_9825.Engine.Repr at out
  have pg : bit 0 target = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs hf (u:=true) (by simp) targetProper
    (out.resolve_right (fun h => h targetProper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have sup : supply true (inputs.map observe) (S.toList.map observe) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact Or.inl (List.mem_map.mpr ⟨v,sub _ (Finset.mem_toList.mp hv),rfl⟩)
  obtain ⟨q,bank,hq,hit,le⟩ := contraction (observe_proper targetProper)
    (list_run run S.toList S.nodup_toList (by simp)) (inputs.map observe) Reach.start sup
  have hl := liftAtThree prior q bank hq hit
  omega
theorem notBudgetOfFace (prior : Lower true (varsX 1015) (graphGoal 1015) 14)
    (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = predicate x) :
    15 + C.gates.countP isNot ≤ C.size := by
  have h := binaryFloorOfFace prior C hf hc
  have split : C.gates.length = C.gates.countP isNot + C.gates.countP (fun g => !isNot g) := by
    simpa using (List.length_eq_countP_add_countP (l:=C.gates) isNot)
  change _ ≤ C.gates.length
  omega

end Research.Signed9822
#print axioms Research.Signed9822.binaryFloorOfFace
#print axioms Research.Signed9822.notBudgetOfFace
