"""Verify raw digests and exhaustively score the four bounded controls."""
import hashlib
import itertools
import json
from pathlib import Path


def controls():
    here = Path(__file__).resolve().parent
    expected = {"positive": True, "outside": False, "conflict": False, "star": False, "split": False}
    for label, yes in expected.items():
        raw = (here / "samples" / (label + ".json")).read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        source = {"star":"EmittedStar","split":"EmittedSplit"}.get(label,"EmittedSamples")
        assert digest in (here / "lean" / ("ThreeName" + source + ".lean")).read_text()
        obj = json.loads(raw)
        assert raw == json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
        columns, pins, (target, a, b) = (obj[k] for k in ("columns", "forced", "names"))
        good = []
        checked = 0
        for bits in itertools.product((False, True), repeat=len(columns)):
            if any(not bits[i] for i in pins):
                continue
            checked += 1
            span = {0}
            for value, chosen in zip(columns, bits):
                if chosen:
                    span |= {x ^ value for x in span}
            if all((((target*y)^(a*u)^(b*v)) in span) == (u == v == 0)
                   for y,u,v in itertools.product(range(2),repeat=3)):
                good.append(tuple(i for i,chosen in enumerate(bits) if chosen))
        assert bool(good) == yes
        if label == "positive":
            assert (0,2,3) in good
        print(label, digest, checked, len(good))


if __name__ == "__main__":
    controls()
