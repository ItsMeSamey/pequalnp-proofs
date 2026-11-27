import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK25 : essentialCheck (25 : Fin 30) = true := by decide +kernel

theorem essentialOK26 : essentialCheck (26 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
