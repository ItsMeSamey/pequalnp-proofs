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
  for module in BoundedOccurrence HallBackdoor HallLeastCore CircuitCounting IncidenceBound FirstGate IncidenceStrict DeletionPacking GateEliminationCost CircuitRewire FirstFanout PlaneRectangleCost PlaneSampleRectangleCost PlaneSixLines DeficiencyOnePivot SparseIncidence IncidenceRobust IncidenceRestrictedRows NatIncidenceRows ResidualFanIn IncidenceInitial IncidenceIterate IncidenceAdditive IncidenceMoments AdaptiveTerminal IncidenceAdaptive AdaptiveGeometry AdaptiveIncidence DeletionThreshold EdgeSamples EdgeCandidate LocalGateCut SparseBoundary UniqueStarCost SparseQueryCut ScalarLocalGates RectangleRowReuse ScalarRankBound SharedLocalSlots PlaneSharedSlots IncidenceRightDerivative BlockCertificate SparseHashLift RegularMatchingDecomposition TwoSidedSlots CycleParity MomentTrade RankOneProjection GuardRelease DiagonalCompletion CyclicGuardChart AffinePigeonhole; do
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
python3 -B "$repo/research/guarded-affine/check_tableau_erasures.py"
python3 -B "$repo/research/polynomial-calculus/check_certificate.py"
python3 -B "$repo/research/guarded-pigeonhole/check.py"
python3 -B "$repo/research/guarded-pigeonhole/mask_lp.py"
python3 -B "$repo/research/guarded-pigeonhole/combined.py"
python3 -B "$repo/research/guarded-pigeonhole/check_separations.py"
python3 -B "$repo/research/guarded-pigeonhole/check_expander.py"
python3 -B "$repo/research/signed-bicliques/check.py"
(
  cd "$repo/research/seed-obstructions"
  python3 -B verify_packing.py L-meta-18968.json packing-18968.json packing-21968.json subset-18968-15.json subset-21968-15.json
)
python3 -B "$repo/research/guarded-pigeonhole/check_sos.py"
python3 -B "$repo/research/incidence-witnesses/check-two-leaf.py"
python3 -B "$repo/research/affine-backdoor/check_backdoor.py"
python3 -B "$repo/research/marker-principal/check.py"
python3 -B "$repo/research/scc-guards/check.py"
python3 -B "$repo/research/chart-basis/check.py"
(cd "$repo/research/signed-cuts" && python3 -B -m unittest)
python3 -B "$repo/research/guarded-pigeonhole/check_unit_exchange.py"
python3 -B "$repo/research/seed-obstructions/verify_mixed.py"
