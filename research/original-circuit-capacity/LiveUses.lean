import ForkWalk
import FirstDivergence

namespace SignedTrace.LiveUses
open PEqualNP.CircuitLowerBounds SignedTrace.ActualUses

/-- Output co-reachability (as distinct from validity of a single physical pin). -/
inductive Live (C : Circuit) (n : Nat) : Nat → Prop where
  | root : Live C n C.output
  | pin {w v p} : Live C n v → FirstDivergence.Live C n w (v,p) → Live C n w

theorem bounded {C : Circuit} {n w : Nat} (h : Live C n w) : w ≤ C.output := by
  induction h with
  | root => omega
  | pin _ hp ih => exact hp.2.1.le.trans ih

noncomputable def keep (C : Circuit) (n : Nat) : Use → Bool := by
  classical
  exact fun u => match u with
    | .pin v _ => decide (Live C n v)
    | .tap _ => true

/-- Actual gate-pin and observation incidences, with dead consumers filtered. -/
noncomputable def outgoing (C : Circuit) (n w : Nat) : List Use :=
  (uses C n w [C.output]).filter (keep C n)

theorem keep_pin {C : Circuit} {n w v p : Nat}
    (h : Use.pin v p ∈ uses C n w [C.output]) (hv : Live C n v) :
    Use.pin v p ∈ outgoing C n w := by
  classical
  exact List.mem_filter.mpr ⟨h,by simpa [keep] using hv⟩

theorem physical_mem {C : Circuit} {n w v p : Nat}
    (h : FirstDivergence.Live C n w (v,p)) :
    Use.pin v p ∈ uses C n w [C.output] := by
  obtain ⟨hn,hw,g,hg,hp,op⟩ := h
  have iz : (g,v-n) ∈ C.gates.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hg
  have hlen := (List.getElem?_eq_some_iff.mp hp).choose
  have hn' : n + (v-n) = v := by omega
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨(g,v-n),iz,?_⟩
  simp only [gateUses,hn']
  apply List.mem_map.mpr
  refine ⟨p,List.mem_filter.mpr ⟨List.mem_range.mpr hlen,?_⟩,rfl⟩
  rcases op with ha | ho | ⟨hnot,hz⟩
  · simp [actualPin,hw,hp,ha]
  · simp [actualPin,hw,hp,ho]
  · change p = 0 at hz
    subst p
    change g.inputs[0]? = some w at hp
    simp [actualPin,hw,hp,hnot]

theorem mem_physical {C : Circuit} {n w v p : Nat}
    (h : Use.pin v p ∈ uses C n w [C.output]) :
    FirstDivergence.Live C n w (v,p) := by
  unfold uses at h
  rcases List.mem_append.mp h with hg | ht
  · obtain ⟨⟨g,j⟩,hj,hp⟩ := List.mem_flatMap.mp hg
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hp
    cases he
    have a := (List.mem_filter.mp hq).2
    have lookup := List.mem_zipIdx_iff_getElem?.mp hj
    refine ⟨by omega,?_,g,by simpa using lookup,?_,?_⟩
    · by_contra! bad
      simp [actualPin,Nat.not_lt_of_ge bad] at a
    · simpa [actualPin,Bool.and_eq_true] using
        ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp a).1).2)
    · cases op : g.op <;> simp_all [actualPin,Bool.and_eq_true]
  · unfold tapUses at ht
    split at ht
    · obtain ⟨_,_,hbad⟩ := List.mem_map.mp ht
      cases hbad
    · simp at ht

theorem pin_iff {C : Circuit} {n w v p : Nat} :
    Use.pin v p ∈ outgoing C n w ↔ FirstDivergence.Live C n w (v,p) ∧ Live C n v := by
  classical
  constructor
  · intro h
    obtain ⟨hm,hv⟩ := List.mem_filter.mp h
    exact ⟨mem_physical hm,by simpa [keep] using hv⟩
  · rintro ⟨h,hv⟩
    exact keep_pin (physical_mem h) hv

theorem run_live {C : Circuit} {n w : Nat} {s t : Bool} {xs : List FirstDivergence.Hop}
    (h : FirstDivergence.Run C n w s C.output t xs) : Live C n w := by
  induction xs generalizing w s with
  | nil => rcases h with ⟨rfl,_⟩; exact .root
  | cons a as ih => exact .pin (ih h.2) h.1

/-- Every edge in an actual reversed certificate appears in the one canonical
live outgoing list at its producer, preserving the consumer and pin position. -/
def Along (C : Circuit) (n : Nat) : Nat → List FirstDivergence.Hop → Prop
  | _, [] => True
  | w, a::xs => Use.pin a.1 a.2 ∈ outgoing C n w ∧ Along C n a.1 xs

theorem run_along {C : Circuit} {n w : Nat} {s t : Bool} {xs : List FirstDivergence.Hop}
    (h : FirstDivergence.Run C n w s C.output t xs) : Along C n w xs := by
  induction xs generalizing w s with
  | nil => trivial
  | cons a as ih => exact ⟨pin_iff.mpr ⟨h.1,run_live h.2⟩,ih h.2⟩

theorem certificate_along {C : Circuit} {n d : Nat} {s : Bool} {hs : Physical.Hops}
    (h : Physical.certificate C n d s hs) : Along C n d hs.reverse :=
  run_along (FirstDivergence.certificate_walk h)

noncomputable def firstFork (C : Circuit) (n w : Nat) : ForkWalk.Walk (outgoing C n) w :=
  match h : outgoing C n w with
  | [] => .unused h
  | [.tap t] => .output t h
  | [.pin v p] =>
    have hp := pin_iff.mp (show Use.pin v p ∈ outgoing C n w by rw [h]; simp)
    have lt : w < v := hp.1.2.1
    have bound : v ≤ C.output := bounded hp.2
    .step v p h (firstFork C n v)
  | a::b::xs => .fork a b xs h
termination_by C.output - w
decreasing_by omega

end SignedTrace.LiveUses
