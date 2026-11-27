import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

/-- A two-edge batch. Each edge has two endpoint choices. -/
abbrev Endpoint := Bool × Bool

/-- Distinct exact transversals on the first batch contain both ends of some
first-batch edge in their union. If they are shared raw clauses, each is also
a transversal on the other two-edge batch. Inducedness on that batch would
then make the same graph edge one of its assigned edges. -/
theorem shared_exact_corner {V : Type*} (adj : V → V → Prop)
    (A B : Endpoint → V) (T : Bool → Bool → Bool)
    (distinct : T false ≠ T true)
    (edges : ∀ i, adj (A (i,false)) (A (i,true)))
    (otherInduced : ∀ s t, adj (B s) (B t) → s.1 = t.1)
    (disjoint : ∀ i j k l, A (i,false) = B (j,k) → A (i,true) ≠ B (j,l))
    (shared : ∀ h i, ∃ e, A (i,T h i) = B e) : False := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, T false i ≠ T true i := by
    by_contra! nope
    exact distinct (funext nope)
  obtain ⟨a,ha⟩ := shared false i
  obtain ⟨b,hb⟩ := shared true i
  have impossible (a b : Endpoint) (ha : A (i,false) = B a) (hb : A (i,true) = B b) : False := by
    have he := edges i
    rw [ha,hb] at he
    obtain ⟨j,k⟩ := a
    obtain ⟨j',l⟩ := b
    have h := otherInduced _ _ he
    change j = j' at h
    subst j'
    exact disjoint i j k l ha hb
  cases h₀ : T false i <;> cases h₁ : T true i
  · exact hi (h₀.trans h₁.symm)
  · exact impossible a b (h₀ ▸ ha) (h₁ ▸ hb)
  · exact impossible b a (h₁ ▸ hb) (h₀ ▸ ha)
  · exact hi (h₀.trans h₁.symm)

/-- The two incident shared blocks may have different neighbors. If their
eligible slots outnumber the entire nonunique set, one shared slot is an
exact witness. Its neighbor's saving is attainable on its own. -/
theorem shared_slot_gain {Slot : Type*} [DecidableEq Slot]
    (A B bad : Finset Slot) (m gain n : ℕ) (ab : Disjoint A B)
    (capacity : bad.card ≤ 2*(n-4))
    (large : 2*(n-4) < A.card+B.card)
    (saveA : ∀ u ∈ A, u ∉ bad → m ≤ gain)
    (saveB : ∀ u ∈ B, u ∉ bad → m ≤ gain) : m ≤ gain := by
  by_contra fail
  have sub : A ∪ B ⊆ bad := by
    intro u hu
    by_contra outside
    rcases Finset.mem_union.mp hu with ha | hb
    · exact fail (saveA u ha outside)
    · exact fail (saveB u hb outside)
  have bound := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint ab] at bound
  omega

/-- n total slots, h edges, and c shared slots with a g-edge neighbor.
A forced unique falsifier covers all g neighbor edges and contains h points. -/
def singleForce (n h c g gain : ℕ) : Prop :=
  2 ≤ h → 2 * (n - 2^h) < c → g ≤ h ∧ g ≤ gain

/-- The ordered rich-pair alternatives, with larger batch first.
The terms for e=1 and e=2 enumerate every positive possibility when s<3. -/
def richPair (a b c r s gain : ℕ) : Prop :=
  2^r + 2^s ≤ a+b-c ∨
  (s < 3 ∧ (2^r ≤ a-c ∨
    (1 ≤ s ∧ 1 ≤ gain ∧ 2^r-2^(r-1) ≤ a-c ∧ 2^r+(if 1<s then 2^(s-1) else 0) ≤ a+b-c) ∨
    (2 ≤ s ∧ 2 ≤ gain ∧ 2^r-2^(r-2) ≤ a-c ∧ 2^r ≤ a+b-c)))

def pairRule (a b c r s gain : ℕ) : Prop :=
  singleForce a r c s gain ∧ singleForce b s c r gain ∧
  (3 ≤ max r s → if s ≤ r then richPair a b c r s gain else richPair b a c s r gain)

/-- Small-batch joint test. The two shared blocks incident to the test root
are distinct occurrences. A tight pair of shared exact clauses is excluded
by shared_exact_corner. -/
def smallRule (n h c g c' g' gain : ℕ) : Prop :=
  h = 2 →
    ((2 * (n-4) < (if 1 ≤ g then c else 0) + (if 1 ≤ g' then c' else 0)) → 1 ≤ gain) ∧
    ((2 * (n-4) < (if 2 ≤ g then c else 0) + (if 2 ≤ g' then c' else 0)) → 2 ≤ gain) ∧
    (n = 4 → g = 2 → c < 2) ∧ (n = 4 → g' = 2 → c' < 2)

theorem exponential_tail (m : ℕ) (hm : 5 ≤ m) : 6*m ≤ 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [pow_succ]; omega


end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
