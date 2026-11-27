import SignedTrace

namespace SignedTrace.ActualUses
open PEqualNP.CircuitLowerBounds

/-- A gate consumer is identified by its output wire and the pin's position
in its input list. A tap is identified by its position in the supplied list
of observed wires, independently of any other tap reading the same wire. -/
inductive Use where
  | pin (consumerWire pinNo : Nat)
  | tap (tapNo : Nat)
  deriving DecidableEq, Repr

/-- A live, physically present operand. AND/OR read every position, NOT
reads only position zero, and self or forward references read a default. -/
def actualPin (g : Gate) (consumerWire producerWire pinNo : Nat) : Bool :=
  decide (producerWire < consumerWire) &&
    (g.inputs[pinNo]? == some producerWire) &&
    (match g.op with
     | .and | .or => true
     | .not => pinNo == 0
     | _ => false)

/-- Enumerate the distinct actual pin positions of one gate reading a wire. -/
def gateUses (g : Gate) (consumerWire producerWire : Nat) : List Use :=
  ((List.range g.inputs.length).filter (actualPin g consumerWire producerWire)).map
    (Use.pin consumerWire)

/-- Enumerate all observed tap positions reading a wire. An invalid output
reference reads the default and does not consume any producer. -/
def tapUses (wireCount producerWire : Nat) (taps : List Nat) : List Use :=
  if producerWire < wireCount then
    ((List.range taps.length).filter (fun t => taps[t]? == some producerWire)).map Use.tap
  else []

/-- All direct pin and tap uses in the supplied circuit and observation list.
Dead gates are included when their actual pins consume the producer. -/
def uses (C : Circuit) (n producerWire : Nat) (taps : List Nat) : List Use :=
  (C.gates.zipIdx.flatMap fun entry =>
    gateUses entry.1 (n + entry.2) producerWire) ++
    tapUses (n + C.gates.length) producerWire taps

def useCount (C : Circuit) (n producerWire : Nat) (taps : List Nat) : Nat :=
  (uses C n producerWire taps).length

/-- The circuit's designated output contributes one tap occurrence. -/
def circuitUseCount (C : Circuit) (n producerWire : Nat) : Nat :=
  useCount C n producerWire [C.output]

theorem no_self_or_forward (g : Gate) (w source pin : Nat) (h : w ≤ source) :
    actualPin g w source pin = false := by
  simp [actualPin, Nat.not_lt_of_ge h]

theorem ignored_not_tail (g : Gate) (w source pin : Nat)
    (hg : g.op = .not) (hp : pin ≠ 0) :
    actualPin g w source pin = false := by
  simp [actualPin, hg, hp]

example : tapUses 2 1 [1, 1, 0] = [.tap 0, .tap 1] := by decide
example : tapUses 2 2 [2] = [] := by decide

end SignedTrace.ActualUses
