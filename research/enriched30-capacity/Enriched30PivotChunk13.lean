import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK15 : essentialCheck (15 : Fin 30) = true := by decide +kernel

theorem essentialOK16 : essentialCheck (16 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
