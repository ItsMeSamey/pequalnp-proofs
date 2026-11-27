import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK27 : essentialCheck (27 : Fin 30) = true := by decide +kernel

theorem essentialOK28 : essentialCheck (28 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
