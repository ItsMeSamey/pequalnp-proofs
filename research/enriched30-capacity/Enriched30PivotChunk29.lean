import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem binateOK4 : binateCheck (4 : Fin 30) = true := by decide +kernel

theorem binateOK7 : binateCheck (7 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
