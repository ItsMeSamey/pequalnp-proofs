import Std

-- SignedRowCut
namespace Petersen9822

def sub (s t : Nat) : Bool := s &&& t == s
def edgeHit (s : Nat) : Bool :=
  ([6,24,17,33,66,132,264,528,160,640,576,320,288] : List Nat).any (fun e => sub e s)
def val (p s u : Nat) := edgeHit (p ||| s ||| u)

structure OneBitAt (p S U : Nat) where
  enc : Nat → Bool
  dec : Bool → Nat → Bool
  correct : ∀ s u, sub s S = true → sub u U = true → val p s u = dec (enc s) u

structure GuardAt (p S U owner : Nat) extends OneBitAt p S U where
  blocking : Bool
  pivotal : ∀ s u, sub s S = true → sub u U = true → sub (u ||| owner) U = true →
    val p s u ≠ val p s (u ||| owner) → enc s = blocking

private theorem differ {p S U a b u : Nat} (h : OneBitAt p S U)
    (ha : sub a S = true) (hb : sub b S = true) (hu : sub u U = true)
    (hd : val p a u ≠ val p b u) : h.enc a ≠ h.enc b := by
  intro eq
  apply hd
  rw [h.correct a u ha hu, h.correct b u hb hu, eq]

theorem triple_sound {p S U a b c j k l : Nat}
    (ha : sub a S = true) (hb : sub b S = true) (hc : sub c S = true)
    (hj : sub j U = true) (hk : sub k U = true) (hl : sub l U = true)
    (hab : val p a j ≠ val p b j) (hac : val p a k ≠ val p c k)
    (hbc : val p b l ≠ val p c l) : ¬ Nonempty (OneBitAt p S U) := by
  rintro ⟨h⟩
  have x := differ h ha hb hj hab
  have y := differ h ha hc hk hac
  have z := differ h hb hc hl hbc
  cases ea : h.enc a <;> cases eb : h.enc b <;> cases ec : h.enc c <;> simp_all

theorem guard_sound {p S U i a b j k l : Nat}
    (ha : sub a S = true) (hb : sub b S = true) (hj : sub j U = true)
    (hk : sub k U = true) (hl : sub l U = true)
    (hk' : sub (k ||| i) U = true) (hl' : sub (l ||| i) U = true)
    (hab : val p a j ≠ val p b j) (hx : val p a k ≠ val p a (k ||| i))
    (hy : val p b l ≠ val p b (l ||| i)) : ¬ Nonempty (GuardAt p S U i) := by
  rintro ⟨h⟩
  apply differ h.toOneBitAt ha hb hj hab
  exact (h.pivotal _ _ ha hk hk' hx).trans (h.pivotal _ _ hb hl hl' hy).symm
end Petersen9822

-- SignedRowWitness

namespace Petersen9822

structure Witness where
  guard : Bool
  prior : Nat
  a : Nat
  b : Nat
  c : Nat
  u : Nat
  v : Nat
  w : Nat
  deriving Repr

def admissible (owner S T U : Nat) : Prop :=
  (∀ p, sub p T = true → Nonempty (OneBitAt p S U)) ∧
  (owner ≠ 0 → ∀ p, sub p T = true → Nonempty (GuardAt p S U owner))

def Witness.check (z : Witness) (owner S T U : Nat) : Bool :=
  sub z.prior T && sub z.a S && sub z.b S && sub z.u U && sub z.v U && sub z.w U &&
  if z.guard then
    decide (owner ≠ 0) && sub (z.v ||| owner) U && sub (z.w ||| owner) U &&
    decide (val z.prior z.a z.u ≠ val z.prior z.b z.u) &&
    decide (val z.prior z.a z.v ≠ val z.prior z.a (z.v ||| owner)) &&
    decide (val z.prior z.b z.w ≠ val z.prior z.b (z.w ||| owner))
  else
    sub z.c S && decide (val z.prior z.a z.u ≠ val z.prior z.b z.u) &&
    decide (val z.prior z.a z.v ≠ val z.prior z.c z.v) &&
    decide (val z.prior z.b z.w ≠ val z.prior z.c z.w)

theorem Witness.sound {z : Witness} {owner S T U : Nat}
    (h : z.check owner S T U = true) : ¬ admissible owner S T U := by
  intro ok
  cases hg : z.guard <;> simp only [Witness.check, hg, Bool.false_eq_true, ite_false,
    ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
  · obtain ⟨⟨⟨⟨⟨⟨hp,ha⟩,hb⟩,hu⟩,hv⟩,hw⟩,⟨⟨⟨hc,hab⟩,hac⟩,hbc⟩⟩ := h
    exact triple_sound ha hb hc hu hv hw hab hac hbc (ok.1 _ hp)
  · obtain ⟨⟨⟨⟨⟨⟨hp,ha⟩,hb⟩,hu⟩,hv⟩,hw⟩,⟨⟨⟨⟨⟨hi,hv'⟩,hw'⟩,hab⟩,hx⟩,hy⟩⟩ := h
    exact guard_sound ha hb hu hv hw hv' hw' hab hx hy (ok.2 hi _ hp)
end Petersen9822

-- SignedCensus
namespace Petersen9822

def ownerBit (j : Nat) := if j < 2 then 2 <<< j else 0
def later (t s : Nat) := 1023 ^^^ (t ||| s)
def legal (j t s : Nat) : Bool :=
  sub s (1023 ^^^ t) && !sub 4 s && (sub 2 s == decide (j = 2)) &&
  !(j < 2 && sub (64 <<< j) s) && !edgeHit s

inductive Placement : List Nat → Nat → Prop where
  | nil {t} : edgeHit (later t 0) = false → Placement [] t
  | cons {j js t s} : s < 1024 → legal j t s = true →
      admissible (ownerBit j) s t (later t s) →
      Placement js (t ||| s) → Placement (j::js) t

abbrev Lookup := Nat → Nat → Nat → Option Witness

def reject (lookup : Lookup) : List Nat → Nat → Bool
  | [],t => edgeHit (later t 0)
  | j::js,t => (List.range 1024).all fun s =>
    !legal j t s || (match lookup j s t with
      | some z => z.check (ownerBit j) s t (later t s)
      | none => false) || reject lookup js (t ||| s)

theorem reject_sound {lookup : Lookup} {js : List Nat} {t : Nat}
    (yes : reject lookup js t = true) : ¬ Placement js t := by
  intro p
  induction p with
  | nil h => simp [reject, h] at yes
  | @cons j js t s hs hl ha tail ih =>
    have hall := (List.all_eq_true.mp yes) s (List.mem_range.mpr hs)
    simp only [hl, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hall
    rcases hall with h | h
    · split at h
      next z hz => exact z.sound h ha
      next => exact Bool.noConfusion h
    · exact ih h
end Petersen9822
