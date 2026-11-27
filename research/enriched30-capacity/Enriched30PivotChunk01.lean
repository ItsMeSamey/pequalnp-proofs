import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK1 : essentialCheck (1 : Fin 30) = true := by decide +kernel

theorem essentialOK2 : essentialCheck (2 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
