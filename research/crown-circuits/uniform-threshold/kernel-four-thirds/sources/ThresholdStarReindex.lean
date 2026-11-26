import ThresholdPinCompiler
import Batteries.Tactic.OpenPrivate
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdPinCompiler ResidualSurplus ThresholdEssentialOr
open private finish_correct finish_mono finish_count from ThresholdPinCompiler
namespace ThresholdStarReindex

inductive Port (k : Nat)
  | fixed (b : Bool)
  | port (i : Fin k)

def wire {k} : Port k → Wire
  | .fixed b => .const b
  | .port j => .live j.val

def assigned {k} (v : List Bool) : Port k → Bool
  | .fixed b => b
  | .port j => v.getD j.val false

def seed {m k} (assign : Fin m → Port k) : State :=
  ⟨[], fun i => if h : i<m then wire (assign ⟨i,h⟩) else .const false⟩

def circuit {m k} (C : Circuit) (assign : Fin m → Port k) : Circuit :=
  finish (compile k C.gates m (seed assign)) k C.output

theorem reindex {m k} (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (assign : Fin m → Port k) :
    let D := circuit C assign
    PEqualNP.MetaComplexity.Monotone2 D ∧ ors D.gates≤ors C.gates ∧
    ∀ v : List Bool, v.length=k → D.eval v=C.eval (List.ofFn (assigned v ∘ assign)) := by
  let start := seed assign
  have sim (v : List Bool) (len : v.length=k) :
      Sim k v (List.ofFn (assigned v ∘ assign)) start := by
    constructor
    · simp [start,seed,basis]
    · intro i
      by_cases h : i<m
      · cases e : assign ⟨i,h⟩ with
        | fixed b => simp [start,seed,h,e,wire,T2BenchmarkNormalize.FitsWire]
        | port j => simpa [start,seed,h,e,wire,T2BenchmarkNormalize.FitsWire] using j.isLt
      · simp [start,seed,h,T2BenchmarkNormalize.FitsWire]
    · intro i
      by_cases h : i<m
      · cases e : assign ⟨i,h⟩ <;>
          simp [start,seed,h,wire,assigned,ResidualSurplus.read,run,List.getD_eq_getElem?_getD,e,Function.comp_def]
      · simp [start,seed,h,ResidualSurplus.read,List.getD_eq_getElem?_getD]
  have endSim (v : List Bool) (len : v.length=k) :
      Sim k v (run C.gates (List.ofFn (assigned v ∘ assign))) (compile k C.gates m start) := by
    simpa only [List.length_ofFn] using sim_scan k v _ start C.gates len mono (sim v len)
  have weak := price_scan k C.gates start (List.replicate m zero) mono
    (by intro i hit; by_cases h : i<m <;> simp [List.getD_eq_getElem?_getD,h,zero] at hit)
  simp only [List.length_replicate] at weak
  refine ⟨finish_mono _ _ _ (endSim (List.replicate k false) (by simp)).mono,?_,?_⟩
  · change ors (finish _ _ _).gates≤_
    rw [finish_count]
    have free : ors start.gs=0 := rfl
    rw [free,Nat.zero_add] at weak
    change ors (compile k C.gates m start).gs ≤ ors C.gates
    omega
  · intro v len
    exact (finish_correct _ _ _ v len).trans ((endSim v len).point C.output)
end ThresholdStarReindex
