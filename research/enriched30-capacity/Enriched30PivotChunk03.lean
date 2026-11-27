import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK4 : essentialCheck (4 : Fin 30) = true := by decide +kernel

theorem essentialOK5 : essentialCheck (5 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
