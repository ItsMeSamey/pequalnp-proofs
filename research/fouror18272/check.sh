#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum --quiet --check SHA256SUMS
python3 -B verify_independent.py
python3 -B verify.py receipts --use-legacy-zero --split32 \
  --confirmation independent/confirmation.json \
  --confirmation-sha256 53eb0df801bdee1f2e30defeb1465231529438b611cab1a34df82478faee2e99 \
  --normalization independent/18272-four-or-independent.tar.gz
