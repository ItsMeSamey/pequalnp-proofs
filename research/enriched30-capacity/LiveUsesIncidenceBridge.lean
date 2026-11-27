import PhysicalLiveIncidence
import LiveUses

namespace ScalarFork.PhysicalLiveIncidence
open PEqualNP.CircuitLowerBounds SignedTrace ScalarFork.LiveIncidence

private theorem slot_member_iff (g : Gate) (i : Nat) :
    i ∈ readSlots g ↔ ∃ p, g.inputs[p]? = some i ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ p = 0)) := by
  cases op : g.op <;> simp [readSlots,op,List.mem_iff_getElem?]
  all_goals cases e : g.inputs <;> simp_all [List.mem_iff_getElem?]
  all_goals rw [← List.mem_iff_getElem?]; simp [eq_comm]

theorem physical_slot_iff {C : Circuit} {n i w : Nat} :
    i ∈ livePins C n w ↔ ∃ p, FirstDivergence.Live C n i (w,p) := by
  constructor
  · intro h
    unfold livePins at h
    cases hg : gateAt C n w with
    | none => simp [hg] at h
    | some g =>
      rw [hg] at h
      obtain ⟨hm,hlt⟩ := List.mem_filter.mp h
      obtain ⟨p,hp,op⟩ := (slot_member_iff g i).mp hm
      have hn : n ≤ w := by
        by_contra! bad
        simp [gateAt,bad] at hg
      exact ⟨p,hn,of_decide_eq_true hlt,g,by simpa [gateAt,Nat.not_lt.mpr hn] using hg,hp,op⟩
  · rintro ⟨p,hn,hlt,g,hg,hp,op⟩
    have mem := (slot_member_iff g i).mpr ⟨p,hp,op⟩
    simp [livePins,gateAt,Nat.not_lt.mpr hn,hg,mem,hlt]

theorem canonical_live_iff {C : Circuit} {n i : Nat} :
    Live C n i ↔ LiveUses.Live C n i := by
  constructor
  · intro h
    induction h with
    | root => exact .root
    | pin _ hp ih =>
      obtain ⟨p,h⟩ := physical_slot_iff.mp hp
      exact .pin ih h
  · intro h
    induction h with
    | root => exact .root
    | pin _ hp ih => exact .pin ih (physical_slot_iff.mpr ⟨_,hp⟩)

theorem canonical_vertices {C : Circuit} {n i : Nat} :
    i ∈ vertices C n ↔ LiveUses.Live C n i :=
  mem_vertices.trans canonical_live_iff

theorem canonical_consumer_iff {C : Circuit} {n i w : Nat} :
    i ∈ livePins C n w ∧ w ∈ vertices C n ↔
      ∃ p, ActualUses.Use.pin w p ∈ LiveUses.outgoing C n i := by
  constructor
  · rintro ⟨hp,hw⟩
    obtain ⟨p,h⟩ := physical_slot_iff.mp hp
    exact ⟨p,LiveUses.pin_iff.mpr ⟨h,canonical_vertices.mp hw⟩⟩
  · rintro ⟨p,h⟩
    obtain ⟨hp,hw⟩ := LiveUses.pin_iff.mp h
    exact ⟨physical_slot_iff.mpr ⟨p,hp⟩,canonical_vertices.mpr hw⟩

private theorem two_gets (xs : List Nat) (x p q : Nat)
    (hp : xs[p]? = some x) (hq : xs[q]? = some x) (hne : p ≠ q) :
    2 ≤ degree x xs := by
  induction xs generalizing p q with
  | nil => simp at hp
  | cons a tail ih =>
    cases p with
    | zero =>
      cases q with
      | zero => exact (hne rfl).elim
      | succ q =>
        have hax : a=x := by simpa using hp
        have hm : x ∈ tail := (List.mem_iff_getElem?).mpr ⟨q,by simpa using hq⟩
        have hpos := degree_pos_iff.mpr hm
        subst a
        simp only [degree,ite_true,eq_self]
        omega
    | succ p =>
      cases q with
      | zero =>
        have hax : a=x := by simpa using hq
        have hm : x ∈ tail := (List.mem_iff_getElem?).mpr ⟨p,by simpa using hp⟩
        have hpos := degree_pos_iff.mpr hm
        subst a
        simp only [degree,ite_true,eq_self]
        omega
      | succ q =>
        have ht := ih p q (by simpa using hp) (by simpa using hq) (by omega)
        simp only [degree]
        omega

private theorem degree_filter_lt (x w : Nat) (h : x<w) (xs : List Nat) :
    degree x (xs.filter (fun i => decide (i<w))) = degree x xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a < w
    · simp [ha,degree,ih]
    · have hx : x ≠ a := by omega
      simp [ha,hx,degree,ih]

theorem two_physical_pins {C : Circuit} {n x w p q : Nat}
    (hp : FirstDivergence.Live C n x (w,p)) (hq : FirstDivergence.Live C n x (w,q))
    (hne : p ≠ q) : 2 ≤ degree x (livePins C n w) := by
  obtain ⟨hn,hlt,g,hg,hp,op⟩ := hp
  obtain ⟨_,_,g',hg',hq,op'⟩ := hq
  rw [hg] at hg'
  cases hg'
  have h := two_gets g.inputs x p q hp hq hne
  have f := degree_filter_lt x w hlt (readSlots g)
  rcases op with hand|hor|⟨hnot,hp0⟩
  · simpa [livePins,gateAt,Nat.not_lt.mpr hn,hg,f,readSlots,hand] using
      (show 2 ≤ degree x ((readSlots g).filter (fun i => decide (i<w))) by
        rw [f]; simpa [readSlots,hand] using h)
  · simpa [livePins,gateAt,Nat.not_lt.mpr hn,hg,f,readSlots,hor] using
      (show 2 ≤ degree x ((readSlots g).filter (fun i => decide (i<w))) by
        rw [f]; simpa [readSlots,hor] using h)
  · rcases op' with ha|ho|⟨_,hq0⟩ <;> simp_all

theorem two_canonical_exits {C : Circuit} {n x w v p q : Nat}
    (hp : ActualUses.Use.pin w p ∈ LiveUses.outgoing C n x)
    (hq : ActualUses.Use.pin v q ∈ LiveUses.outgoing C n x)
    (hne : (w,p) ≠ (v,q)) : 2 ≤ fanout C n x := by
  classical
  obtain ⟨ap,wp⟩ := LiveUses.pin_iff.mp hp
  obtain ⟨aq,vq⟩ := LiveUses.pin_iff.mp hq
  let S := vertices C n
  have hw : w ∈ S := canonical_vertices.mpr wp
  have hv : v ∈ S := canonical_vertices.mpr vq
  let d := fun z => degree x (livePins C n z)
  change 2 ≤ ∑ z ∈ S, d z
  by_cases e : w=v
  · subst v
    have two := two_physical_pins ap aq (fun eq => hne (by rw [eq]))
    exact two.trans (Finset.single_le_sum (f:=d) (fun _ _ => Nat.zero_le _) hw)
  · have one : 1 ≤ d w := degree_pos_iff.mpr (physical_slot_iff.mpr ⟨p,ap⟩)
    have other : 1 ≤ d v := degree_pos_iff.mpr (physical_slot_iff.mpr ⟨q,aq⟩)
    have hv' : v ∈ S.erase w := Finset.mem_erase.mpr ⟨Ne.symm e,hv⟩
    have bound := Finset.single_le_sum (f:=d) (fun _ _ => Nat.zero_le _) hv'
    rw [← Finset.sum_erase_add S d hw]
    omega

/-- Nonraw proof objects stay in the pinned program. The source count consists
of actual live physical input wire IDs, before any identification of values. -/
theorem source_count (C : Circuit) (n : Nat) :
    (∑ w ∈ vertices C n, sourceCharge n w) =
      ((vertices C n).filter (fun w => w < n)).card :=
  Finset.sum_boole (R := Nat) (fun w => w<n) (vertices C n)

/-- Count directly from distinct exits in the canonical live outgoing list. -/
theorem canonical_capacity (C : Circuit) (n : Nat) (occupied : Finset Nat)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (forked : ∀ x ∈ occupied, ∃ w p v q,
      ActualUses.Use.pin w p ∈ LiveUses.outgoing C n x ∧
      ActualUses.Use.pin v q ∈ LiveUses.outgoing C n x ∧ (w,p) ≠ (v,q)) :
    ((vertices C n).filter (fun w => w < n)).card + occupied.card ≤
      (∑ w ∈ vertices C n, binCharge C n w) + 1 := by
  classical
  have sub : occupied ⊆ (vertices C n).filter (fun i => 2 ≤ fanout C n i) := by
    intro x hx
    obtain ⟨w,p,v,q,hp,hq,ne⟩ := forked x hx
    obtain ⟨edge,consumer⟩ := LiveUses.pin_iff.mp hp
    exact Finset.mem_filter.mpr ⟨canonical_vertices.mpr (.pin consumer edge),
      two_canonical_exits hp hq ne⟩
  rw [←source_count]
  exact (Nat.add_le_add_left (Finset.card_le_card sub) _).trans
    (physical_capacity_of_fanin C n cap)

end ScalarFork.PhysicalLiveIncidence
