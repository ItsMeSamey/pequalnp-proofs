import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK6 : essentialCheck (6 : Fin 30) = true := by decide +kernel

theorem essentialOK7 : essentialCheck (7 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
