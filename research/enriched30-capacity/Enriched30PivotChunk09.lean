import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK11 : essentialCheck (11 : Fin 30) = true := by decide +kernel

theorem essentialOK12 : essentialCheck (12 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
