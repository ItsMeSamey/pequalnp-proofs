import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK8 : essentialCheck (8 : Fin 30) = true := by decide +kernel

theorem essentialOK9 : essentialCheck (9 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
