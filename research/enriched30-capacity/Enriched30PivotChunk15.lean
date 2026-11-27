import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK17 : essentialCheck (17 : Fin 30) = true := by decide +kernel

theorem essentialOK18 : essentialCheck (18 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
