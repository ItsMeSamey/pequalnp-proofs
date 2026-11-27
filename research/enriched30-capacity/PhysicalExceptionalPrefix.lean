import LiveUses
import ExceptionalPrefixCard

namespace SignedTrace.PhysicalExceptional
open PEqualNP.CircuitLowerBounds ActualUses ForkWalk FirstDivergence
open ForkCertificates

/-- The first branch, lone observation, or unused endpoint of a physical walk. -/
def stop {f : Nat → List Use} {w : Nat} : ForkWalk.Walk f w → Nat
  | .unused _ | .output _ _ | .fork _ _ _ _ => w
  | .step _ _ _ tail => stop tail

theorem stop_unique {f : Nat → List Use} {w : Nat} (a : ForkWalk.Walk f w) :
    ∀ b : ForkWalk.Walk f w, stop a = stop b := by
  induction a with
  | unused h =>
    intro b
    cases b with
    | unused _ | output _ _ | fork _ _ _ _ => rfl
    | step _ _ h' _ => have bad := h.symm.trans h'; simp at bad
  | output t h =>
    intro b
    cases b with
    | unused _ | output _ _ | fork _ _ _ _ => rfl
    | step _ _ h' _ => have bad := h.symm.trans h'; simp at bad
  | fork x y xs h =>
    intro b
    cases b with
    | unused _ | output _ _ | fork _ _ _ _ => rfl
    | step _ _ h' _ => have bad := h.symm.trans h'; simp at bad
  | step v i h tail ih =>
    intro b
    cases b with
    | unused h' => have bad := h.symm.trans h'; simp at bad
    | output t h' => have bad := h.symm.trans h'; simp at bad
    | fork x y xs h' => have bad := h.symm.trans h'; simp at bad
    | step v' i' h' tail' =>
      have eq : v = v' := by grind
      subst v'
      exact ih tail'

noncomputable def firstStop (C : Circuit) (n w : Nat) : Nat :=
  stop (LiveUses.firstFork C n w)

abbrev LWalk (C : Circuit) (n w : Nat) := ForkWalk.Walk (LiveUses.outgoing C n) w

/-- The source is an ordinary donor; count an inversion on entry to its
consumer, including a NOT at the stop, never double-counting that stop. -/
def prefixSign {C : Circuit} {n w : Nat} : LWalk C n w → Bool → Bool
  | .unused _, s | .output _ _, s | .fork _ _ _ _, s => s
  | .step v i _ tail, s => prefixSign tail (nextSign C n (v,i) s)

noncomputable def inverters (C : Circuit) (n : Nat) : Finset Nat := by
  classical
  exact (Finset.range (n+C.gates.length)).filter fun w =>
    n ≤ w ∧ LiveUses.Live C n w ∧ (C.gates[w-n]?).map Gate.op = some .not

private theorem flip_mem {C : Circuit} {n w : Nat} {h : Hop} {s : Bool}
    (e : FirstDivergence.Live C n w h) (live : LiveUses.Live C n h.1)
    (hf : nextSign C n h s ≠ s) : h.1 ∈ inverters C n := by
  classical
  obtain ⟨hn, _, g, hg, _, _⟩ := e
  have bound := (List.getElem?_eq_some_iff.mp hg).choose
  have op : g.op = .not := by
    cases eq : g.op <;> simp_all [nextSign]
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn,live,by simp [hg,op]⟩

private theorem le_stop {C : Circuit} {n w : Nat} (p : LWalk C n w) : w ≤ stop p := by
  induction p with
  | unused _ => exact Nat.le_refl _
  | output _ _ => exact Nat.le_refl _
  | fork _ _ _ _ => exact Nat.le_refl _
  | @step w v i h tail ih =>
    have hp := LiveUses.pin_iff.mp (show Use.pin v i ∈ LiveUses.outgoing C n w by rw [h]; simp)
    exact hp.1.2.1.le.trans ih

private theorem prefix_flip {C : Circuit} {n w : Nat} (p : LWalk C n w) :
    ∀ s, prefixSign p s ≠ s →
      ∃ a ∈ inverters C n, firstStop C n a = stop p ∧ a ≤ stop p := by
  induction p with
  | unused _ => simp [prefixSign]
  | output _ _ => simp [prefixSign]
  | fork _ _ _ _ => simp [prefixSign]
  | @step w v i h tail ih =>
    intro s hf
    by_cases he : nextSign C n (v,i) s = s
    · exact ih s (by simpa [prefixSign,he] using hf)
    · have hp := LiveUses.pin_iff.mp (show Use.pin v i ∈ LiveUses.outgoing C n w by rw [h]; simp)
      exact ⟨v,flip_mem hp.1 hp.2 he,stop_unique (LiveUses.firstFork C n v) tail,le_stop tail⟩

/-- Strip the complete deterministic prefix, even when a particular pair of
physical certificates happens to follow the same pin at an earlier fork. -/
private theorem strip {C : Circuit} {n w : Nat} (p : LWalk C n w) :
    ∀ {s t xs}, Run C n w s C.output t xs →
      ∃ ys, Run C n (stop p) (prefixSign p s) C.output t ys := by
  induction p with
  | unused _ => intro s t xs h; exact ⟨xs,h⟩
  | output _ _ => intro s t xs h; exact ⟨xs,h⟩
  | fork _ _ _ _ => intro s t xs h; exact ⟨xs,h⟩
  | @step w v i h tail ih =>
    intro s t xs hr
    have hp := LiveUses.pin_iff.mp (show Use.pin v i ∈ LiveUses.outgoing C n w by rw [h]; simp)
    cases xs with
    | nil =>
      have hw := hr.1
      have ha := hp.1.2.1
      have hb := LiveUses.bounded hp.2
      omega
    | cons hop xs =>
      have hm := (LiveUses.run_along hr).1
      have e : hop = (v,i) := by
        rcases hop with ⟨a,b⟩
        simpa [h] using hm
      subst hop
      exact ih hr.2

private theorem later_flip {C : Circuit} {n w : Nat} {s t : Bool} {xs : List Hop}
    (hr : Run C n w s C.output t xs) (hne : s ≠ t) :
    ∃ b ∈ inverters C n, w < b := by
  induction xs generalizing w s with
  | nil => exact (hne hr.2).elim
  | cons h hs ih =>
    by_cases eq : nextSign C n h s = s
    · obtain ⟨b,hb,hlt⟩ := ih hr.2 (by simpa [eq] using hne)
      exact ⟨b,hb,Nat.lt_trans hr.1.2.1 hlt⟩
    · exact ⟨h.1,flip_mem hr.1 (LiveUses.run_live hr.2) eq,hr.1.2.1⟩

theorem physical_prefix_witness {C : Circuit} {n d : Nat}
    {even odd : Physical.Hops}
    (he : Physical.certificate C n d false even)
    (_ho : Physical.certificate C n d true odd)
    (hp : prefixSign (LiveUses.firstFork C n d) false = true) :
    ∃ a ∈ inverters C n, firstStop C n a = firstStop C n d ∧
      ∃ b ∈ inverters C n, a < b := by
  let p := LiveUses.firstFork C n d
  obtain ⟨a,ha,hstop,hle⟩ := prefix_flip p false (by simp [p,hp])
  obtain ⟨ys,hy⟩ := strip p (FirstDivergence.certificate_walk he)
  obtain ⟨b,hb,hlt⟩ := later_flip hy (by simp [p,hp])
  exact ⟨a,ha,hstop,b,hb,Nat.lt_of_le_of_lt hle hlt⟩

theorem physical_exceptional_card (C : Circuit) (n : Nat) (groups : Finset Nat)
    (hex : ∀ g ∈ groups, ∃ d even odd, firstStop C n d = g ∧
      Physical.certificate C n d false even ∧ Physical.certificate C n d true odd ∧
      prefixSign (LiveUses.firstFork C n d) false = true) :
    groups.card ≤ (inverters C n).card - 1 := by
  apply exceptional_card_le_inverter_card_sub_one groups (inverters C n) id (firstStop C n)
  intro g hg
  obtain ⟨d,even,odd,rfl,he,ho,hp⟩ := hex g hg
  exact physical_prefix_witness he ho hp

/-- The physical input donors witnessing an exceptional first branch. -/
noncomputable def exceptionalGroups (C : Circuit) (n : Nat) : Finset Nat := by
  classical
  exact ((Finset.range n).filter fun d =>
    (∃ even, Physical.certificate C n d false even) ∧
    (∃ odd, Physical.certificate C n d true odd) ∧
    prefixSign (LiveUses.firstFork C n d) false = true).image (firstStop C n)

theorem actual_exceptional_card (C : Circuit) (n : Nat) :
    (exceptionalGroups C n).card ≤ (inverters C n).card - 1 := by
  classical
  apply physical_exceptional_card
  intro g hg
  obtain ⟨d,hd,hg⟩ := Finset.mem_image.mp hg
  obtain ⟨_,⟨even,he⟩,⟨odd,ho⟩,hp⟩ := Finset.mem_filter.mp hd
  exact ⟨d,even,odd,hg,he,ho,hp⟩

theorem subset_erase_latest (C : Circuit) (n last : Nat)
    (_hl : last ∈ inverters C n) (hmax : ∀ b ∈ inverters C n, b ≤ last) :
    exceptionalGroups C n ⊆ ((inverters C n).erase last).image (firstStop C n) := by
  classical
  intro g hg
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨_,⟨even,he⟩,⟨odd,ho⟩,hp⟩ := Finset.mem_filter.mp hd
  obtain ⟨a,ha,heq,b,hb,hlt⟩ := physical_prefix_witness he ho hp
  have hne : a ≠ last := by
    have := hmax b hb
    omega
  exact Finset.mem_image.mpr ⟨a,Finset.mem_erase.mpr ⟨hne,ha⟩,heq⟩

end SignedTrace.PhysicalExceptional
