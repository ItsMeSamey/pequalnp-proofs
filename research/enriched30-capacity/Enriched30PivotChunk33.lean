import Enriched30PivotCore

namespace Enriched30Pivot

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem binateOK14 : binateCheck (14 : Fin 30) = true := by decide +kernel

theorem binateOK16 : binateCheck (16 : Fin 30) = true := by decide +kernel

end Enriched30Pivot
