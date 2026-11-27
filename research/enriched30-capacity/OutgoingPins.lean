import LiveUses
import Mathlib.Data.List.Nodup

namespace SignedTrace.OutgoingPins
open PEqualNP.CircuitLowerBounds SignedTrace.ActualUses SignedTrace.LiveUses

private theorem pinShape {g : Gate} {v w : Nat} {u : Use} (hu : u ∈ gateUses g v w) :
    ∃ p, u = .pin v p := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hu
  exact ⟨p,rfl⟩

private theorem tapShape {k w : Nat} {ts : List Nat} {u : Use} (hu : u ∈ tapUses k w ts) :
    ∃ p, u = .tap p := by
  unfold tapUses at hu
  split at hu
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hu
    exact ⟨p,rfl⟩
  · simp at hu

theorem outgoing_nodup (C : Circuit) (n w : Nat) : (outgoing C n w).Nodup := by
  unfold outgoing
  apply List.Nodup.filter
  unfold uses
  apply List.nodup_append'.mpr
  constructor
  · apply List.nodup_flatMap.mpr
    constructor
    · intro a _
      apply List.Nodup.map (fun x y h => by injection h)
      exact List.Nodup.filter _ List.nodup_range
    · have hn : (C.gates.zipIdx.map Prod.snd).Nodup := by
        rw [List.zipIdx_map_snd]
        exact List.nodup_range' _
      have hp : C.gates.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := List.pairwise_map.mp hn
      apply hp.imp
      intro a b h u hu hv
      obtain ⟨p, rfl⟩ := pinShape hu
      obtain ⟨q, eq⟩ := pinShape hv
      injection eq with he
      exact h (Nat.add_left_cancel he)
  constructor
  · unfold tapUses
    split
    · apply List.Nodup.map (fun x y h => by injection h)
      exact List.Nodup.filter _ List.nodup_range
    · simp
  · intro u hu hv
    obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hu
    obtain ⟨p, rfl⟩ := pinShape ha
    obtain ⟨q, he⟩ := tapShape hv
    cases he

private theorem tap_info {C : Circuit} {n w t : Nat}
    (h : Use.tap t ∈ outgoing C n w) : w = C.output ∧ t = 0 := by
  have hm := (List.mem_filter.mp h).1
  rcases List.mem_append.mp hm with hg | ht
  · obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hg
    obtain ⟨p, he⟩ := pinShape ha
    cases he
  · unfold tapUses at ht
    split at ht
    · obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
      have hit : i = t := Use.tap.inj he
      obtain ⟨hr, hv⟩ := List.mem_filter.mp hi
      have iz : i = 0 := by
        have := List.mem_range.mp hr
        simp at this
        omega
      refine ⟨?_, hit.symm.trans iz⟩
      rw [iz] at hv
      have hw : C.output = w := by simpa using hv
      exact hw.symm
    · simp at ht

private theorem no_mixed {C : Circuit} {n w t v p : Nat}
    (ht : Use.tap t ∈ outgoing C n w) (hp : Use.pin v p ∈ outgoing C n w) : False := by
  obtain ⟨hw,_⟩ := tap_info ht
  obtain ⟨he,hl⟩ := pin_iff.mp hp
  have lt : w < v := he.2.1
  have le := bounded hl
  omega

theorem two_pins {C : Circuit} {n w : Nat} (h : 2 ≤ (outgoing C n w).length) :
    ∃ v p z q, Use.pin v p ∈ outgoing C n w ∧ Use.pin z q ∈ outgoing C n w ∧
      (v,p) ≠ (z,q) := by
  obtain ⟨a,b,rest,he⟩ : ∃ a b rest, outgoing C n w = a :: b :: rest := by
    cases hh : outgoing C n w with
    | nil => simp [hh] at h
    | cons a xs =>
      cases xs with
      | nil => simp [hh] at h
      | cons b rest => exact ⟨a,b,rest,rfl⟩
  have ha : a ∈ outgoing C n w := by simp [he]
  have hb : b ∈ outgoing C n w := by simp [he]
  have nd := outgoing_nodup C n w
  rw [he] at nd
  have ne : a ≠ b := by
    intro eq
    exact (List.nodup_cons.mp nd).1 (by simp [eq])
  cases a with
  | pin v p =>
    cases b with
    | pin z q =>
      exact ⟨v,p,z,q,ha,hb,fun eq => by cases eq; exact ne rfl⟩
    | tap t => exact (no_mixed hb ha).elim
  | tap t =>
    cases b with
    | pin z q => exact (no_mixed ha hb).elim
    | tap u =>
      have et := (tap_info ha).2
      have eu := (tap_info hb).2
      exact (ne (by rw [et,eu])).elim

end SignedTrace.OutgoingPins
