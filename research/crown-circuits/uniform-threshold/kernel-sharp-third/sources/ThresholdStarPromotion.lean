import ThresholdStarEndpointRows
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource ThresholdSimpleIncidence

/-- Each selected block is the opposite endpoint of some star edge and has a
different star edge for the empty and own-singleton comparisons. The criterion
does not assume correctness of either the overridden or bypassed circuit. -/
theorem promoted_threshold_trace {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (sel : Nat → Bool) (u : T2OrPartition.Id (source gs out))
    (star : Finset (Fin n)) (nonempty : star.Nonempty)
    (incident : ∀ y∈star,u∈endpoints (layout n gs out M.eligible) y)
    (selected : ∀ p t, Block.group p t ∈ forest (layout n gs out M.eligible) Fin.val →
      t.out≠n+u.val → sel t.out=true →
      ∃ (x y : Fin n) (v : T2OrPartition.Id (source gs out)), x∈star ∧ y∈star ∧ x≠y ∧
        endpoints (layout n gs out M.eligible) x ⊆ {u,v} ∧ t.out=n+v.val)
    (s : Finset (Fin n)) (sub : s⊆star) :
    let bs := forest (layout n gs out M.eligible) Fin.val
    let raw := fun j => (vector s).getD j false
    ((run (n+u.val) sel true raw bs (fun _ => false) out ||
      taps (n+u.val) sel raw bs (fun _ => false))=true ↔ 2≤s.card) ∧
      (s.card<2 → taps (n+u.val) sel raw bs (fun _ => false)=false) := by
  intro bs raw
  let L := layout n gs out M.eligible
  let old := fun (r : Finset (Fin n)) => run (n+u.val) sel false
    (fun j => (vector r).getD j false) bs (fun _ => false) out
  have sem (r : Finset (Fin n)) (rs : r⊆star) : old r=true ↔ 2≤r.card := by
    by_cases pos : r.Nonempty
    · obtain ⟨y,hy⟩ := pos
      exact forced_nonempty_row M reg sel r y u hy (incident y (rs hy))
    · have eq : r=∅ := Finset.not_nonempty_iff_eq_empty.mp pos
      subst r
      obtain ⟨y,hy⟩ := nonempty
      have one := forced_nonempty_row M reg sel {y} y u (by simp) (incident y hy)
      have grow : Below (fun j => (vector (∅ : Finset (Fin n))).getD j false)
          (fun j => (vector {y}).getD j false) := by
        intro j
        change (vector (∅ : Finset (Fin n))).getD j false=true → _
        rw [vec_get]; split <;> simp
      have mono := scan_monotone (n+u.val) sel false _ _ grow bs (fun _ => false)
        (fun _ => false) (fun _ h => h)
      constructor
      · intro h
        have contra := one.mp (mono out h)
        simp at contra
      · simp
  have neg (fail : old s=false) : ArmsOff (n+u.val) sel raw bs (fun _ => false) := by
    have small : s.card<2 := by
      by_contra! large
      have yes := (sem s sub).mpr large
      rw [yes] at fail
      contradiction
    apply all_off_of_split
    intro pre b post split
    cases b with
    | meet => rfl
    | group p t =>
      by_cases force : t.out=n+u.val
      · simp [tap,force]
      by_cases select : sel t.out=true
      · have hb : Block.group p t∈bs := by rw [split]; simp
        obtain ⟨x,y,v,hx,hy,xy,pair,root⟩ := selected p t hb force select
        have both := empty_self_arm_off M reg sel x y xy u v (incident y hy) pair pre post p t split root
        have clearArm : t.exts.any (run (n+u.val) sel false raw pre (fun _ => false))=false := by
          rcases Nat.eq_zero_or_pos s.card with zero|positive
          · obtain rfl := Finset.card_eq_zero.mp zero
            exact both.1
          · obtain ⟨z,hz⟩ := Finset.card_eq_one.mp (by omega : s.card=1)
            subst s
            by_cases eq : z=x
            · subst z; exact both.2
            · exact singleton_arm_off M reg sel x z (Ne.symm eq) u v (incident z (sub (by simp)))
                pair pre post p t split root
        simp [tap,force,select,clearArm]
      · simp [tap,select]
  constructor
  · rw [promoted_same _ _ _ _ _ _ neg]
    exact sem s sub
  · intro small
    apply all_off
    apply neg
    cases e : old s with
    | false => rfl
    | true => have h := (sem s sub).mp e; omega
theorem promoted_threshold {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (sel : Nat → Bool) (u : T2OrPartition.Id (source gs out))
    (star : Finset (Fin n)) (nonempty : star.Nonempty)
    (incident : ∀ y∈star,u∈endpoints (layout n gs out M.eligible) y)
    (selected : ∀ p t, Block.group p t ∈ forest (layout n gs out M.eligible) Fin.val →
      t.out≠n+u.val → sel t.out=true →
      ∃ (x y : Fin n) (v : T2OrPartition.Id (source gs out)), x∈star ∧ y∈star ∧ x≠y ∧
        endpoints (layout n gs out M.eligible) x ⊆ {u,v} ∧ t.out=n+v.val)
    (s : Finset (Fin n)) (sub : s⊆star) :
    let bs := forest (layout n gs out M.eligible) Fin.val
    let raw := fun j => (vector s).getD j false
    (run (n+u.val) sel true raw bs (fun _ => false) out ||
      taps (n+u.val) sel raw bs (fun _ => false))=true ↔ 2≤s.card := by
  exact (promoted_threshold_trace M reg sel u star nonempty incident selected s sub).1
#print axioms promoted_threshold
end ThresholdStarBypass
