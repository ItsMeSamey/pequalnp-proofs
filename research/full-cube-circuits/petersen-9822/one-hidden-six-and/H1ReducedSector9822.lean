import H1ReducedPriced9822
import H1CoverAllDirect9822
namespace Research.H1Cover
open Research.H1Price PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FreeAndNet.CircuitCompiler
open PEqualNP.Outside.L_meta_9822.Clean PEqualNP.Outside.L_meta_9822.Sectors
theorem reduced_one_hidden (gs : List Gate) (o : Nat) (red : ReducedCandidate gs o)
    (zero : gs.countP countsNot=0) (six : gs.countP countsAnd=6)
    (one : (physicalHidden (⟨gs,o⟩ : Circuit)).card=1) : False :=
  reduced_sector_one_hidden_with_prices (fun small ok => allCharged small ok) gs o red zero six one
theorem original_reduced_one_hidden (C : Circuit) (cand : Candidate C)
    (red : Reduced 10 C.gates C.output) (zero : C.gates.countP countsNot=0)
    (six : C.gates.countP countsAnd=6) (one : (physicalHidden C).card=1) : False :=
  reduced_one_hidden_with_prices (fun small ok => allCharged small ok) C cand red zero six one
end Research.H1Cover
#print axioms Research.H1Cover.reduced_one_hidden
#print axioms Research.H1Cover.original_reduced_one_hidden
