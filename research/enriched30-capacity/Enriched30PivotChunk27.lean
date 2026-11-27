import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem essentialOK29 : essentialCheck (29 : Fin 30) = true := by decide +kernel

theorem binateOK2 : binateCheck (2 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
