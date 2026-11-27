import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem binateOK8 : binateCheck (8 : Fin 30) = true := by decide +kernel

theorem binateOK9 : binateCheck (9 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
