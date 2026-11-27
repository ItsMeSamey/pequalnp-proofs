"""Generate typed original-ID certificates for positive and early negative answers."""
import argparse
import hashlib
import json
from pathlib import Path


def _reduce(word, tag, pivots):
    while word:
        pivot = word.bit_length() - 1
        if pivot not in pivots:
            break
        row, rhs = pivots[pivot]
        word ^= row
        tag ^= rhs
    return word, tag


def _indexed_basis(cols, ids):
    pivots = {}
    for i in ids:
        row, mask = _reduce(cols[i], 1 << i, pivots)
        if row:
            pivots[row.bit_length() - 1] = row, mask
    return pivots


def _bits(mask):
    ids = []
    while mask:
        bit = mask & -mask
        ids.append(bit.bit_length() - 1)
        mask ^= bit
    return ids


def _separator(equations):
    """Solve parity(row & x) = rhs by elimination, with free bits zero."""
    pivots = {}
    for x, rhs in equations:
        row, value = _reduce(x, rhs, pivots)
        if row:
            pivots[row.bit_length() - 1] = row, value
        elif value:
            raise ValueError("no separating parity row for this claim")
    mask = 0
    for pivot, (row, rhs) in sorted(pivots.items()):
        if (row & mask).bit_count() % 2 != rhs:
            mask |= 1 << pivot
    return _bits(mask)


def _ids(values, count):
    if not isinstance(values, list) or any(type(i) is not int or i not in range(count) for i in values):
        raise ValueError("invalid original position list")
    return values


def produce(raw, transcript):
    """Return verified local arguments. The input digest excludes the transcript."""
    if set(raw) != {"columns", "names", "forced"}:
        raise ValueError("raw input needs columns, names, forced")
    cols, names = raw["columns"], raw["names"]
    if (not isinstance(cols, list) or not isinstance(names, list) or len(names) != 3
            or any(type(x) is not int or x < 0 for x in cols + names)):
        raise ValueError("invalid packed word input")
    if len(_indexed_basis(names, range(3))) != 3:
        raise ValueError("expected three independent names")
    n = len(cols)
    pins = _ids(raw["forced"], n)
    digest = hashlib.sha256(json.dumps(raw, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    out = {"sha256": digest, "width": max(cols + names).bit_length(),
           "columns": cols, "pins": pins, "names": names}
    t, a, b = names
    kind = transcript["terminal"]
    if kind in ("pins_witness", "single", "excluded"):
        support = _ids(transcript["support"], n)
        if len(support) != len(set(support)) or not set(pins) <= set(support):
            raise ValueError("support must contain all pins exactly as original positions")
        rem, mask = _reduce(t, 0, _indexed_basis(cols, support))
        if rem:
            raise ValueError("target is not in the selected original span")
        zero = [(cols[i], 0) for i in support]
        return out | {"kind":"positive", "selected":sorted(set(support) - set(pins)),
                      "witness":_bits(mask), "rowA":_separator(zero + [(a, 1), (b, 0)]),
                      "rowB":_separator(zero + [(a, 0), (b, 1)])}
    if kind == "pins_conflict":
        table = _indexed_basis(cols, pins)
        for u, v in ((True, False), (False, True), (True, True)):
            for y in (False, True):
                word = (a if u else 0) ^ (b if v else 0) ^ (t if y else 0)
                rem, mask = _reduce(word, 0, table)
                if not rem:
                    return out | {"kind":"conflict", "u":u, "v":v, "y":y, "witness":_bits(mask)}
        raise ValueError("no off-axis named sum supported by original pins")
    if kind == "outside":
        return out | {"kind":"outside", "row":_separator([(c, 0) for c in cols] + [(t, 1)])}
    raise ValueError("requires a positive support, pin conflict, or outside-target claim")


def lean_source(raw, transcript):
    cert = produce(raw, transcript)
    width, n = cert["width"], len(cert["columns"])
    target, a, b = cert["names"]
    names = f"{target} {a} {b}"
    pins = cert["pins"]
    out = ["import ThreeNameGenericDirect", "namespace DirectInstance_" + cert["sha256"],
           "open ThreeNamePacked ThreeNamePinReduction ThreeNameGenericPositive ThreeNameGenericDirect",
           f'def rawInputSHA256 : String := "{cert["sha256"]}"',
           f'abbrev ID := Fin {n}',
           f'def col (i : ID) : BitVec {width} := ({cert["columns"]} : List (BitVec {width})).getD i.val 0']
    exact = f"Exact (fun i => decode (col i)) (named {names})"
    if cert["kind"] == "positive":
        sel, witness = cert["selected"], cert["witness"]
        args = f'col {pins} {sel} {names} {witness} {cert["rowA"]} {cert["rowB"]}'
        out += [f'theorem checked : check {args} = true := by decide',
                f'theorem result : ({pins} : List ID).toFinset ⊆ support {pins} {sel} ∧',
                f'    {exact} (support {pins} {sel}) := sound {args} checked']
    elif cert["kind"] == "conflict":
        flags = " ".join(str(cert[k]).lower() for k in ("u", "v", "y"))
        args = f'col {pins} {names} {flags} {cert["witness"]}'
        out += [f'theorem checked : checkConflict {args} = true := by decide',
                f'theorem result (A : Finset ID) (h : ({pins} : List ID).toFinset ⊆ A) :',
                f'    ¬ {exact} A := conflict_no {args} checked A h']
    else:
        row = cert["row"]
        out += [f'theorem checked : checkOutside col {target} {row} = true := by decide',
                f'theorem result (A : Finset ID) : ¬ {exact} A :=',
                f'  outside_no col {names} {row} checked A']
    out += ["#print axioms result", "end DirectInstance_" + cert["sha256"]]
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw", type=Path)
    parser.add_argument("transcript", type=Path)
    parser.add_argument("--format", choices=("lean", "json"), default="lean")
    args = parser.parse_args()
    raw_data, trace = (json.loads(path.read_text()) for path in (args.raw, args.transcript))
    print(lean_source(raw_data, trace) if args.format == "lean" else
          json.dumps(produce(raw_data, trace), sort_keys=True, indent=2), end="\n")
