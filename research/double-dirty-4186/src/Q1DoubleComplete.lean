import Q1DoubleRealizedComplete
import DDGraphCap

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

/-- The issued positive cover inequality for the one-charged-OR slice in which
both input wires of the unique charged OR are outputs of dirty AND gates. -/
theorem complete : DoubleDirtyCase :=
  completeOfRealization (fun s => s.cap_realization)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
