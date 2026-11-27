import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK13 : essentialCheck (13 : Fin 30) = true := by decide +kernel

theorem essentialOK14 : essentialCheck (14 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
