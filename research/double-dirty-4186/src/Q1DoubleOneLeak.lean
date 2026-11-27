import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

/-- A position records which residual edge and which endpoint of that edge. A
pattern selects one endpoint from each of the two external residual edges. -/
abbrev Pos := Bool × Bool
abbrev Pattern := Bool × Bool

def includes (t : Pattern) (p : Pos) : Prop :=
  p.2 = (if p.1 then t.2 else t.1)

instance (t : Pattern) (p : Pos) : Decidable (includes t p) := by unfold includes; infer_instance

private theorem two_patterns : ∀ t s : Pattern, t ≠ s → ∀ p q : Pos,
    includes t p → includes s p → includes t q → includes s q → p = q := by decide

private theorem three_patterns : ∀ t s u : Pattern, t ≠ s → t ≠ u → s ≠ u →
    ∀ p : Pos, includes t p → includes s p → ¬ includes u p := by decide

variable {V : Type*} {label : Pos → V} {T : Finset Pattern}
variable {fresh : V → V → Prop}

/-- Slot supports are *exactly* the two labeled endpoints of their pattern. -/
def inSlot (label : Pos → V) (t : Pattern) (x : V) : Prop :=
  ∃ p, includes t p ∧ label p = x

/-- Each assigned fresh edge meets each of the shared slots. Two vertices from the
external matching cannot form an assigned fresh edge (inducedness and exclusivity). -/
theorem common_position (inj : Function.Injective label)
    (separate : ∀ p q, ¬ fresh (label p) (label q))
    (meet : ∀ a b, fresh a b → ∀ t ∈ T, inSlot label t a ∨ inSlot label t b)
    (hne : T.Nonempty) {a b} (hab : fresh a b) :
    ∃ p, (label p = a ∨ label p = b) ∧ ∀ t ∈ T, includes t p := by
  classical
  obtain ⟨t,ht⟩ := hne
  rcases meet a b hab t ht with ⟨p,_,rfl⟩ | ⟨p,_,rfl⟩
  · refine ⟨p, Or.inl rfl, ?_⟩
    intro u hu
    rcases meet _ _ hab u hu with ⟨q,hq,eq⟩ | ⟨q,_,rfl⟩
    · exact inj eq ▸ hq
    · exact (separate p q hab).elim
  · refine ⟨p, Or.inr rfl, ?_⟩
    intro u hu
    rcases meet _ _ hab u hu with ⟨q,_,rfl⟩ | ⟨q,hq,eq⟩
    · exact (separate q p hab).elim
    · exact inj eq ▸ hq

theorem three_shared_impossible (inj : Function.Injective label)
    (separate : ∀ p q, ¬ fresh (label p) (label q))
    (meet : ∀ a b, fresh a b → ∀ t ∈ T, inSlot label t a ∨ inSlot label t b)
    {t s u : Pattern} (ht : t ∈ T) (hs : s ∈ T) (hu : u ∈ T)
    (ts : t ≠ s) (tu : t ≠ u) (su : s ≠ u) : ∀ a b, ¬ fresh a b := by
  intro a b hab
  obtain ⟨p,_,hp⟩ := common_position inj separate meet ⟨t,ht⟩ hab
  exact three_patterns t s u ts tu su p (hp t ht) (hp s hs) (hp u hu)

/-- When at least one fresh edge exists, two distinct exact shared slots expose
one labeled external endpoint that also covers *every* fresh edge. -/
theorem two_shared_hub (inj : Function.Injective label)
    (separate : ∀ p q, ¬ fresh (label p) (label q))
    (meet : ∀ a b, fresh a b → ∀ t ∈ T, inSlot label t a ∨ inSlot label t b)
    {t s : Pattern} (ht : t ∈ T) (hs : s ∈ T) (ts : t ≠ s) (nonempty : ∃ a b, fresh a b) :
    ∃ p, ∀ a b, fresh a b → label p = a ∨ label p = b := by
  obtain ⟨a,b,hab⟩ := nonempty
  obtain ⟨p,_,hp⟩ := common_position inj separate meet ⟨t,ht⟩ hab
  refine ⟨p, ?_⟩
  intro x y hxy
  obtain ⟨q,hq,hits⟩ := common_position inj separate meet ⟨t,ht⟩ hxy
  have eq := two_patterns t s ts p q (hp t ht) (hp s hs) (hits t ht) (hits s hs)
  exact eq.symm ▸ hq

private theorem linear_strict {h : ℕ} (hh : 3 ≤ h) : 2*h < 2^h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih => rw [pow_succ]; omega

/-- The singleton external gate costs one unit when its two occurrences are identified. -/
theorem two_slack {h y : ℕ} (hy : 3 ≤ y) (hp : 0 < h → 2^h ≤ y) :
    2*h+1 ≤ y ∨ (h=2 ∧ y=4) := by
  by_cases large : 3 ≤ h
  · have := linear_strict large
    have := hp (by omega)
    omega
  · interval_cases h <;> norm_num at * <;> omega

theorem two_private {a b w y privateCost h : ℕ} (privateBound : privateCost ≤ a+b+w)
    (slack : 2*h+1 ≤ y) : privateCost+2*h ≤ a+b+w+y-1 := by omega

theorem two_exact {a b w r s saving : ℕ} (ha : 2 ≤ a) (hr : r ≤ 1)
    (hs : 2*s ≤ b+w) (hsave : r=1 → 1 ≤ saving) :
    2*(r+s+2) ≤ (a+b+w+4-1)+saving := by omega

theorem pow_six {m : ℕ} (hm : 5 ≤ m) : 6*m ≤ 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih => rw [pow_succ]; omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
