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
  for module in BoundedOccurrence HallBackdoor HallLeastCore CircuitCounting IncidenceBound FirstGate IncidenceStrict DeletionPacking GateEliminationCost CircuitRewire FirstFanout PlaneRectangleCost PlaneSampleRectangleCost PlaneSixLines DeficiencyOnePivot SparseIncidence IncidenceRobust IncidenceRestrictedRows NatIncidenceRows ResidualFanIn IncidenceInitial IncidenceIterate IncidenceAdditive IncidenceMoments AdaptiveTerminal IncidenceAdaptive AdaptiveGeometry AdaptiveIncidence DeletionThreshold EdgeSamples EdgeCandidate LocalGateCut SparseBoundary UniqueStarCost SparseQueryCut ScalarLocalGates RectangleRowReuse ScalarRankBound SharedLocalSlots PlaneSharedSlots IncidenceRightDerivative BlockCertificate SparseHashLift RegularMatchingDecomposition TwoSidedSlots CycleParity MomentTrade RankOneProjection GuardRelease DiagonalCompletion; do
    echo "Checking Research.$module"
    lean -DwarningAsError=true -o "$2/Research/$module.olean" "Research/$module.lean"
  done
' bash "$repo" "$build_dir"
python3 -B "$repo/research/hall-solver/verify.py"
python3 -B "$repo/research/hall-solver/check_deficiency_one.py"
python3 -B "$repo/research/violation-moments/check.py"
python3 -B "$repo/research/violation-moments/check_indexed.py"
python3 -B "$repo/research/rank-projection/check_rank_projection.py"
python3 -B "$repo/research/fiber-solver/check.py"
python3 -B "$repo/research/fiber-solver/check_edges.py"
python3 -B "$repo/research/guarded-affine/check.py"
python3 -B "$repo/research/guarded-affine/symmetric.py"
python3 -B "$repo/research/guarded-affine/check_charts.py"
