import T2RawIsolation

namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RawIsolation

def ren (h x j : Nat) := if j<h then j else if j=h then x else j-1
def rewire (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
def short (n x : Nat) (pre post : List Gate) (out : Nat) : Circuit :=
  let f := ren (n+pre.length) x
  ⟨pre ++ post.map (rewire f),f out⟩
def moved (n x p : Nat) (pre post : List Gate) (out : Nat) : Circuit :=
  let J := short n x pre post out
  ⟨J.gates ++ [binary .or J.output p],n+J.gates.length⟩

theorem same_size (n x p : Nat) (pre post : List Gate) (out : Nat) :
    (moved n x p pre post out).gates.length = (pre ++ binary .or x p :: post).length := by
  simp [moved,short] <;> omega

theorem kind_list (n x p : Nat) (pre post : List Gate) (out : Nat) :
    (moved n x p pre post out).gates.map Gate.op =
      pre.map Gate.op ++ post.map Gate.op ++ [GateOp.or] := by
  simp [moved,short,rewire,List.map_map,Function.comp_def,binary,gateOp]

theorem pair_forces_clean (pre post : List Gate) (x p out : Nat) (u v : List Bool)
    (off : AgreeOff x u v) (notOut : out ≠ x) (diff : p ≠ x)
    (left : ∀ row∈pre, x∉row.inputs) (right : ∀ row∈post, x∉row.inputs)
    (separates : (run (pre ++ binary .or x p :: post) u).getD out false ≠
      (run (pre ++ binary .or x p :: post) v).getD out false) :
    (run pre u).getD p false = false := by
  have hp := (unread_run pre off left).2 p diff
  cases hv : (run pre u).getD p false with
  | false => rfl
  | true =>
    exfalso
    apply separates
    apply isolated_reader pre post (binary .or x p) off notOut left right
    have hv' : (run pre v).getD p false = true := hp.symm.trans hv
    simp only [List.getD_eq_getElem?_getD] at hv hv'
    simp [val,binary,gateOp,GateOp.eval,hv,hv']

def vector {n : Nat} (s : Finset (Fin n)) : List Bool := List.ofFn (fun i => decide (i∈s))
def Computes (n : Nat) (C : Circuit) : Prop :=
  ∀ s : Finset (Fin n), C.eval (vector s) = true ↔ 2 ≤ s.card

noncomputable def hotRows (n : Nat) (C : Circuit) : Nat := by
  classical
  exact ((List.range C.gates.length).filter (fun j =>
    decide (∃ i : Fin n, (C.wires (vector {i})).getD (n+j) false = true))).length

def Eligible (n : Nat) (C : Circuit) : Prop := Computes n C ∧ C.output<n+C.gates.length ∧
  ∀ j : Fin C.gates.length, (C.gates[j].op=GateOp.and ∨ C.gates[j].op=GateOp.or) ∧
    C.gates[j].inputs.length=2 ∧ ∀ a∈C.gates[j].inputs, a<n+j.val

def SecondaryMinimum (n : Nat) (C : Circuit) :=
  ∀ D, Eligible n D → D.size=C.size → hotRows n C ≤ hotRows n D

/-- Pending physical suffix simulation and hot-row injection. -/
def EditClaim (n x p : Nat) (pre post : List Gate) (out : Nat) : Prop :=
  let C : Circuit := ⟨pre ++ binary .or x p :: post,out⟩
  let D := moved n x p pre post out
  Eligible n C → x<n → p<n+pre.length →
  (∀ s : Finset (Fin n), s.card<2 → (run pre (vector s)).getD p false=false) →
  Eligible n D ∧ hotRows n D < hotRows n C

theorem excludes_at_secondary_minimum (n x p : Nat) (pre post : List Gate) (out : Nat)
    (edit : EditClaim n x p pre post out)
    (hc : Eligible n ⟨pre ++ binary .or x p :: post,out⟩)
    (minimal : SecondaryMinimum n ⟨pre ++ binary .or x p :: post,out⟩)
    (hx : x<n) (hp : p<n+pre.length)
    (clean : ∀ s : Finset (Fin n), s.card<2 → (run pre (vector s)).getD p false=false) : False := by
  obtain ⟨hd,strict⟩ := edit hc hx hp clean
  have weak := minimal (moved n x p pre post out) hd (same_size n x p pre post out)
  omega
end T2SoleOrSplice
