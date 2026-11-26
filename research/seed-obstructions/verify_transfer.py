"""Check the projected domination and zero columns used in raw-to-residual transfer."""
from pathlib import Path
from verify_packing import require, samples

rows, front, target = samples(Path(__file__).with_name("L-meta-18968.json"))
live = (1 << 38) - 1
require(front & ~target == 0, "front contains a negative")
require(front & target & 1 and not ((target >> 52) & 1), "invalid domination pair")
positive, negative = rows[0] & live, rows[52] & live
require((positive, negative) == (74089234433, 239451881479), "incorrect projections")
require(not positive & ~negative, "front-positive projection escapes the negative")
residual_rows = {row for i, row in enumerate(rows) if ((target ^ front) >> i) & 1}
require(len(residual_rows) == 28 and all(row >> 38 == 0 for row in residual_rows),
        "omitted inputs do not vanish on the residual positives")
print("Verified the raw domination pair and all seven zero columns on the 28 residual positives.")
