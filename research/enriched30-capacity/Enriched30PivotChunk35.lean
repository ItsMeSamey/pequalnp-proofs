import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem binateOK20 : binateCheck (20 : Fin 30) = true := by decide +kernel

theorem binateOK22 : binateCheck (22 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
