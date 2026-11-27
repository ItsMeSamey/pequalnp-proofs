import H1OriginalWitness9822
import H1CoverAllOriginalH19822
import SixH1NonleakyOriginal9822
namespace Research.H1Cover
open Research.H1Price PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FreeAndNet.CircuitCompiler
open PEqualNP.Outside.L_meta_9822.Clean PEqualNP.Outside.L_meta_9822.Sectors
open Research.Graph9822H2Check (negative)
theorem original_six_one_floor (C : Circuit) (cand : Candidate C) (clean : CleanL 10 C.gates)
    (zero : C.gates.countP countsNot=0) (six : C.gates.countP countsAnd=6)
    (one : (physicalHidden C).card=1) : 12 ≤ (C.gates.filter orFlag).length := by
  obtain ⟨w⟩ := original_witness C cand clean zero six one
  let sig := hiddenSig (scopeMask w.A) (scopeMask w.B)
  by_cases leak : negative sig≠0
  · exact allOriginalH1 C.gates C.output w.hidden w.A w.B _ w.exposed w.cap w.raw leak
      w.arms w.uses w.hot w.cold
  · apply nonleaky_original C.gates C.output w.hidden w.A w.B _ w.exposed w.cap w.raw
      w.arms w.uses sig rfl _ w.hot w.cold
    intro i
    have hz : negative sig=0 := by simpa using leak
    have h := congrArg (fun n : Nat => n.testBit i.val) hz
    simpa [negative,Nat.testBit_shiftRight] using h
end Research.H1Cover
#print axioms Research.H1Cover.original_six_one_floor
