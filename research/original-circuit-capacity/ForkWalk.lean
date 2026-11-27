import ActualUses

namespace SignedTrace.ForkWalk

open PEqualNP.CircuitLowerBounds SignedTrace.ActualUses

private theorem pin_bounds (C : Circuit) (n w v pin : Nat) (taps : List Nat)
    (h : Use.pin v pin ∈ uses C n w taps) : w < v ∧ v < n + C.gates.length := by
  unfold uses at h
  rcases List.mem_append.mp h with hg | ht
  · obtain ⟨e, he, hp⟩ := List.mem_flatMap.mp hg
    unfold gateUses at hp
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp hp
    cases eq
    have hpos := (List.mem_filter.mp hp).2
    have hi := List.snd_lt_of_mem_zipIdx he
    by_cases hlt : w < n + e.2
    · exact ⟨hlt, by omega⟩
    · simp [actualPin, hlt] at hpos
  · unfold tapUses at ht
    split at ht
    · obtain ⟨_, _, hbad⟩ := List.mem_map.mp ht
      cases hbad
    · simp at ht

/-- Each continuation records the sole consuming pin. A terminal records the
exact observation list, including distinct occurrences with the same consumer. -/
inductive Walk (outgoing : Nat → List Use) : Nat → Type where
  | unused {w} (h : outgoing w = []) : Walk outgoing w
  | output {w} (tap : Nat) (h : outgoing w = [.tap tap]) : Walk outgoing w
  | fork {w} (a b : Use) (rest : List Use) (h : outgoing w = a :: b :: rest) :
      Walk outgoing w
  | step {w} (v pin : Nat) (h : outgoing w = [.pin v pin]) (tail : Walk outgoing v) :
      Walk outgoing w

/-- Follow the actual outgoing incidences of a circuit, stopping at the first
branch, sole observation, or unused wire. The number of higher wire indices
strictly decreases along each recursive call. -/
def firstFork (C : Circuit) (n : Nat) (taps : List Nat) (w : Nat) :
    Walk (fun v => uses C n v taps) w :=
  match h : uses C n w taps with
  | [] => .unused h
  | [.tap t] => .output t h
  | [.pin v p] =>
    have hb := pin_bounds C n w v p taps (by rw [h]; simp)
    .step v p h (firstFork C n taps v)
  | a :: b :: rest => .fork a b rest h
termination_by n + C.gates.length - w
decreasing_by omega

end SignedTrace.ForkWalk
