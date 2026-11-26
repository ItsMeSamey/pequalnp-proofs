#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
mkdir -p "$build_dir/Research"
cd "${PNP_LAKE_DIR:-$repo/lean}"
lake build PEqualNP.Defs.TopForm
lake env bash -eu -o pipefail -c '
  cd "$1/lean"
  export LEAN_PATH="$2:$LEAN_PATH"
  for module in BoundedOccurrence HallBackdoor HallLeastCore CircuitCounting IncidenceBound FirstGate IncidenceStrict DeletionPacking GateEliminationCost CircuitRewire FirstFanout PlaneRectangleCost PlaneSampleRectangleCost PlaneSixLines DeficiencyOnePivot SparseIncidence IncidenceRobust IncidenceRestrictedRows NatIncidenceRows ResidualFanIn IncidenceInitial IncidenceIterate IncidenceAdditive IncidenceMoments AdaptiveTerminal IncidenceAdaptive AdaptiveGeometry AdaptiveIncidence DeletionThreshold EdgeSamples EdgeCandidate; do
    echo "Checking Research.$module"
    lean -DwarningAsError=true -o "$2/Research/$module.olean" "Research/$module.lean"
  done
' bash "$repo" "$build_dir"
python3 -B "$repo/research/hall-solver/verify.py"
python3 -B "$repo/research/hall-solver/check_deficiency_one.py"
