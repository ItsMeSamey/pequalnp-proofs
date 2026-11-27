import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK21 : essentialCheck (21 : Fin 30) = true := by decide +kernel

theorem essentialOK22 : essentialCheck (22 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
