import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem binateOK25 : binateCheck (25 : Fin 30) = true := by decide +kernel

theorem binateOK28 : binateCheck (28 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
