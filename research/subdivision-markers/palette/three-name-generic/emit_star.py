"""Emit a typed generic host invocation for a supplied star transcript."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

base = Path(__file__).resolve().parent
sys.path.insert(0, str(base.parent / "three-name-refinement"))
from generate import array, extract, fs


def pin_basis(cols, pins):
    basis = {}
    for i in pins:
        v, mask = cols[i], 1 << i
        while v:
            j = v.bit_length()-1
            if j not in basis:
                basis[j] = v, mask
                break
            y, indices = basis[j]
            v, mask = v ^ y, mask ^ indices
    return sorted(basis.items(), reverse=True)


def project(x, basis):
    for j, (v, _) in basis:
        if x >> j & 1:
            x ^= v
    return x


def emit(row):
    raw = {key:row[key] for key in ("columns","names","forced")}
    cols, names, pins = (raw[key] for key in ("columns","names","forced"))
    if (len(names) != 3 or any(type(v) is not int or v < 0 for v in cols+names)
            or any(type(i) is not int or not 0 <= i < len(cols) for i in pins)):
        raise ValueError("invalid raw input")
    pins = sorted(set(pins))
    free = [i for i in range(len(cols)) if i not in pins]
    pivot = pin_basis(cols,pins)
    projection = {"columns":[project(cols[i],pivot) for i in free],"forced":[],
                  "names":[project(v,pivot) for v in names],"certificate":row["certificate"]}
    vals,w,gs,steps,edges,h,inc,fwd,rev = extract(projection)
    width = max([w]+[v.bit_length() for v in cols+names])
    def extend(rows):
        return list(rows)+[0]*(width-w)
    n = len(vals)
    lift = {i:6+j for j,i in enumerate(free)}
    lift.update({i:n+j for j,i in enumerate(pins)})
    n += len(pins)
    rawbytes = json.dumps(raw,sort_keys=True,separators=(",",":")).encode()
    dig = hashlib.sha256(rawbytes).hexdigest()
    s = ["import ThreeNameGenericHost","namespace ThreeNameEmittedStar",
         "open ThreeNamePacked ThreeNameGenericTrail ThreeNamePinReduction",
         "set_option maxRecDepth 30000","set_option maxHeartbeats 4000000",
         f'def rawDigest : String := "{dig}"', f"abbrev O := Fin {len(cols)}",f"abbrev J := Fin {n}",
         array("raw","O",f"BitVec {width}",cols),f"def pins : List O := {pins}",
         f"def pivots : ThreeNamePackedPins.Table {width} := {[(j,v) for j,(v,_) in pivot]}",
         f"def supports (j : Fin {width}) : List O := match j.val with"]
    for j, (_,mask) in pivot:
        s.append(f"  | {j} => {[i for i in range(len(cols)) if mask>>i&1]}")
    s += ["  | _ => []",array("words","J",f"BitVec {width}",vals),
          array("attach","O","J",[lift[i] for i in range(len(cols))]),
          "def lift : O ↪ J := ⟨attach, by decide⟩"]
    for k,g in enumerate(gs):
        s.append(f"def p{k} : Frame J {width} := ⟨{fs(g,'J')},words⟩")
    for k,(keep,rows,tab) in enumerate(steps):
        s.extend([array(f"m{k}",f"Fin {width}",f"BitVec {width}",extend(rows)),
            f"def j{k} : Jump ({{0,1,2}} : Finset J) p{k} p{k+1} := " +
            f"⟨{fs(keep,'J')},m{k},{fs(tab,f'BitVec {width}')}, by decide⟩"])
    last = len(steps)
    trail = ".nil p"+str(last)
    for k in reversed(range(last)):
        trail = f".cons j{k} ({trail})"
    s.append(f"def trail : Trail ({{0,1,2}} : Finset J) p0 p{last} := "+trail)
    vertex = set(edges[0]) & set(edges[1]) & set(edges[2])
    if not vertex:
        raise ValueError("missing terminal center")
    tails, heads, incs = ([0]*n for _ in range(3))
    for i,(u,v),z in zip(gs[-1],edges,inc,strict=True):
        tails[i],heads[i],incs[i]=u,v,z
    for name,dom,typ,data in [("l","J",f"Fin {h}",tails),("r","J",f"Fin {h}",heads),
            ("inc","J",f"BitVec {h}",incs),("fwd",f"Fin {h}",f"BitVec {width}",fwd),
            ("back",f"Fin {width}",f"BitVec {h}",extend(rev))]:
        s.append(array(name,dom,typ,data))
    t,a,b=names
    s.extend([f"def terminal : Terminal p{last} 0 1 2 {h} :=",
        f"  ⟨inc,l,r,{min(vertex)},fwd,back,by decide,by decide,by decide⟩",
        "theorem no (A : Finset O) (hp : pins.toFinset ⊆ A) :",
        f"    ¬ Exact (fun i => decode (raw i)) (ThreeNameGenericPositive.named ({t} : BitVec {width}) {a} {b}) A :=",
        f"  ThreeNameGenericHost.rejects raw pins {t} {a} {b} pivots supports (by decide)",
        f"    p0 p{last} 0 1 2 lift (by decide) (by decide) trail terminal A hp",
        "#print axioms no","end ThreeNameEmittedStar"])
    namespace = "ThreeNameEmittedStar" if not steps else "ThreeNameEmittedSplit" + dig[:12]
    return rawbytes, ("\n".join(s)+"\n").replace("ThreeNameEmittedStar",namespace)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("transcript","raw_output","lean_output"):
        parser.add_argument(name,type=Path)
    args=parser.parse_args()
    raw,source=emit(json.loads(args.transcript.read_text()))
    args.raw_output.write_bytes(raw)
    args.lean_output.write_text(source)
