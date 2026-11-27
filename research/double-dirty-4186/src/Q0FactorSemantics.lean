import Q0FactorRows
import Q0Readers
import Graph18272Bridge

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux.S4183.S98

/-- Original wires reached from the distinguished gate using only AND readers. -/
inductive AndPath (n : ℕ) (C : Circuit) (g : ℕ) : ℕ → Prop
  | source : AndPath n C g (n+g)
  | step {w j : ℕ} (before : AndPath n C g w) (hj : j < C.gates.length)
      (hand : (gateAt C j).op = .and) (pin : w ∈ (gateAt C j).inputs) :
      AndPath n C g (n+j)

noncomputable def affected (n : ℕ) (C : Circuit) (g j : ℕ) : Bool := by
  classical
  exact decide (AndPath n C g (n+j))

private noncomputable def phase {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g k : ℕ) : Layout n :=
  ((List.range k).map (rowOf G C g)).foldl next (seed n)

private theorem phase_succ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g k : ℕ) : phase G C g (k+1) =
      next (phase G C g k) (rowOf G C g k) := by
  simp [phase, List.range_succ, List.foldl_append]

private theorem phase_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g k : ℕ) : (phase G C g k).slots.length = n+k := by
  induction k with
  | zero => simp [phase, seed]
  | succ k ih =>
    rw [phase_succ]
    generalize rowOf G C g k = r
    obtain ⟨kind,a,b⟩ := r
    cases kind <;> simp [next, ih, Nat.add_assoc]

private theorem read_old {n : ℕ} (s : Layout n) (r : Row) {w : ℕ} (hw : w < s.slots.length) :
    readPin (next s r) w = readPin s w := by
  obtain ⟨kind,a,b⟩ := r
  cases kind <;> simp [readPin, next, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

private def added {n : ℕ} (s : Layout n) (r : Row) : Option (Signal n) :=
  match r.kind with
  | .source | .cleanOr => none
  | .product => project (readPin s r.left) (readPin s r.right)
  | .disjunction => projectedOr (readPin s r.left) (readPin s r.right)

private theorem read_added {n : ℕ} (s : Layout n) (r : Row) :
    readPin (next s r) s.slots.length = added s r := by
  obtain ⟨kind,a,b⟩ := r
  cases kind <;> simp [readPin, next, added, List.getD_eq_getElem?_getD]

private theorem path_ge {n : ℕ} {C : Circuit} {g w : ℕ} (hAO : IsAO2 n C)
    (hp : AndPath n C g w) : n+g ≤ w := by
  induction hp with
  | source => exact le_rfl
  | step prev hj hand pin ih => exact ih.trans (Nat.le_of_lt (hAO.2.1 _ hj _ pin))

private theorem path_prod {n : ℕ} {C : Circuit} {g j a b : ℕ} (hne : j ≠ g)
    (hj : j < C.gates.length) (ha : (gateAt C j).op = .and)
    (pins : (gateAt C j).inputs = [a,b]) :
    AndPath n C g (n+j) ↔ AndPath n C g a ∨ AndPath n C g b := by
  constructor
  · intro h
    generalize he : n+j = out at h
    cases h with
    | source => omega
    | @step w k prev hk hand pin =>
      have eq : k = j := by omega
      subst k
      rw [pins] at pin
      rcases (by simpa using pin : w = a ∨ w = b) with rfl | rfl
      · exact Or.inl prev
      · exact Or.inr prev
  · rintro (h | h)
    · exact .step h hj ha (by simp [pins])
    · exact .step h hj ha (by simp [pins])

private theorem path_or {n : ℕ} {C : Circuit} {g j : ℕ} (hne : j ≠ g)
    (hor : (gateAt C j).op = .or) : ¬ AndPath n C g (n+j) := by
  intro hp
  generalize he : n+j = out at hp
  cases hp with
  | source => omega
  | @step w k prev hk hand pin =>
    have eq : k = j := by omega
    subst k
    simp_all

/-- Omitted clean ORs are intentionally excluded from original-wire reconstruction. -/
def Kept {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) :=
  ∀ j ∈ orT G C, w ≠ n+j

/-- Structural facts about reader pins, independent of the evaluation assignment. -/
structure PinRules {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) : Prop where
  kept : ∀ j < C.gates.length, j ∉ orT G C → ∀ w ∈ (gateAt C j).inputs, Kept G C w
  plain : ∀ j < C.gates.length, j ∉ orT G C → (gateAt C j).op = .or →
    ∀ w ∈ (gateAt C j).inputs, ¬ AndPath n C g w

private abbrev old {n : ℕ} (C : Circuit) (w : ℕ) : Signal n := fun x => W n C x w

private def Models {n : ℕ} (src v : Signal n) (bit : Bool) (r : Option (Signal n)) : Prop :=
  (bit = false → r ≠ none) ∧ ∀ x, v x = (if bit then src x && denotation r x else denotation r x)

private theorem and_models {n : ℕ} {s a b : Signal n} {p q : Option (Signal n)} {u v : Bool}
    (ha : Models s a u p) (hb : Models s b v q) :
    Models s (join true a b) (u || v) (project p q) := by
  constructor
  · intro hz
    cases u <;> cases v <;> simp_all only [Bool.or_false, Bool.or_true, Bool.false_eq_true,
      Bool.true_eq_false, not_false_eq_true]
    all_goals cases hp : p <;> cases hq : q <;> simp_all [Models, project]
  · intro x
    have h1 := ha.2 x
    have h2 := hb.2 x
    rw [projected_value]
    cases u <;> cases v <;> cases hs : s x <;> simp_all [join]

private theorem or_models {n : ℕ} {s a b : Signal n} {p q : Option (Signal n)}
    (ha : Models s a false p) (hb : Models s b false q) :
    Models s (join false a b) false (projectedOr p q) := by
  cases p <;> cases q <;> simp_all [Models, projectedOr, join, denotation, funext_iff]

private theorem models_false {n : ℕ} (s v : Signal n) (r : Option (Signal n)) :
    Models s v false r ↔ r = some v := by
  cases r with
  | none => simp [Models]
  | some f =>
    constructor
    · intro h
      exact congrArg some (funext fun x => (h.2 x).symm)
    · rintro h
      injection h with h
      subst f
      exact ⟨by simp, fun _ => rfl⟩

private theorem sources_keep {n : ℕ} (s : Layout n) (r : Row) (v : Option (Signal n))
    (hv : v ∈ s.sources) : v ∈ (next s r).sources := by
  obtain ⟨k,a,b⟩ := r
  cases k <;> simp [next, hv]

set_option maxHeartbeats 3000000 in
theorem top_wire_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hAO : IsAO2 n C) (hg : g ∈ junk G C) (rules : PinRules G C g) :
    (∀ B, Good B (doneLayout G C g) → B (gateVal n C g)) ∧
    ∀ t ∈ tops G C, ∀ x, gateVal n C t x =
      (if affected n C g t then gateVal n C g x && denotation
        (readPin (doneLayout G C g) (n+t)) x else
        denotation (readPin (doneLayout G C g) (n+t)) x) := by
  classical
  obtain ⟨hglen, hgand, _⟩ := (S4183.junk_iff G C g).mp hg
  let src : Signal n := old C (n+g)
  let flag := fun w => decide (AndPath n C g w)
  have inv (k : ℕ) (hk : k ≤ C.gates.length) :
      (∀ w < n+k, Kept G C w → Models src (old C w) (flag w) (readPin (phase G C g k) w)) ∧
      (g < k → some src ∈ (phase G C g k).sources) := by
    induction k with
    | zero =>
      refine ⟨?_, by omega⟩
      intro w hw _
      have hw' : w < n := by omega
      have hn : ¬ AndPath n C g w := fun h => by have := path_ge hAO h; omega
      rw [show flag w = false by simp [flag, hn], models_false]
      have he : old C w = fun x => x ⟨w,hw'⟩ := funext fun x => W_input n C x w hw'
      simp [phase, seed, readPin, List.getD_eq_getElem?_getD, hw', he]
    | succ j ih =>
      have hj : j < C.gates.length := by omega
      obtain ⟨prev, prevSrc⟩ := ih (by omega)
      let s := phase G C g j
      let a := opnd C j 0
      let b := opnd C j 1
      have len : s.slots.length = n+j := phase_length G C g j
      obtain ⟨hops,p,q,hpq,hp,hq⟩ := AO_of_IsAO2 n C hAO j hj
      have ea : a = p := by simp [a, opnd, hpq]
      have eb : b = q := by simp [b, opnd, hpq]
      have pins : (gateAt C j).inputs = [a,b] := by simpa [ea,eb] using hpq
      have ha : a < n+j := by simpa only [ea] using hp
      have hb : b < n+j := by simpa only [eb] using hq
      have ma : a ∈ (gateAt C j).inputs := by simp [pins]
      have mb : b ∈ (gateAt C j).inputs := by simp [pins]
      have regs (hn : j ∉ orT G C) :=
        And.intro (prev a ha (rules.kept j hj hn a ma)) (prev b hb (rules.kept j hj hn b mb))
      have andEq (op : (gateAt C j).op = .and) :
          old C (n+j) = join true (old C a) (old C b) :=
        funext fun x => W_and n C x j hj op a b pins ha hb
      have orEq (op : (gateAt C j).op = .or) :
          old C (n+j) = join false (old C a) (old C b) :=
        funext fun x => W_or n C x j hj op a b pins ha hb
      have sourcePiece (e : j = g) :
          project (readPin s a) (readPin s b) = some src := by
        have op : (gateAt C j).op = .and := by simpa [e] using hgand
        have hn : j ∉ orT G C := fun h => by
          have hh := (Finset.mem_filter.mp h).2.1
          simp_all
        obtain ⟨h1,h2⟩ := regs hn
        have hpa : ¬ AndPath n C g a := fun h => by have := path_ge hAO h; omega
        have hpb : ¬ AndPath n C g b := fun h => by have := path_ge hAO h; omega
        simp only [flag, decide_eq_false hpa, decide_eq_false hpb] at h1 h2
        have hh := (models_false ..).mp (and_models h1 h2)
        change project (readPin (phase G C g j) a) (readPin (phase G C g j) b) = some (old C (n+g))
        simpa only [← andEq op, e] using hh
      rw [phase_succ]
      constructor
      · intro w hw keep
        by_cases hbefore : w < n+j
        · rw [read_old _ _ (by simpa only [phase_length] using hbefore)]
          exact prev w hbefore keep
        have eq : w = n+j := by omega
        subst w
        change Models _ _ _ (readPin (next s _) (n+j))
        rw [← len, read_added]
        have hn : j ∉ orT G C := fun h => keep j h rfl
        by_cases e : j = g
        · have hf : flag (n+j) = true := by
            apply decide_eq_true
            simpa only [e] using (AndPath.source (n:=n) (C:=C) (g:=g))
          simp [added, rowOf, e, hf, Models, src, denotation, len, flag, AndPath.source]
        · obtain ⟨h1,h2⟩ := regs hn
          rcases hops with hand | hor
          · have hflag : flag (n+j) = (flag a || flag b) := by
              simp [flag, path_prod e hj hand pins]
            simpa only [len, andEq hand, hflag, added, rowOf, if_neg e, if_neg hn, if_pos hand, a, b]
              using and_models h1 h2
          · have hna := rules.plain j hj hn hor a ma
            have hnb := rules.plain j hj hn hor b mb
            have hh := path_or (n:=n) e hor
            simp only [flag, decide_eq_false hna, decide_eq_false hnb] at h1 h2
            simpa [added, rowOf, e, hn, hor, a, b, orEq hor, flag, hh, len] using or_models h1 h2
      · intro hjg
        by_cases e : j = g
        · have hs := sourcePiece e
          change some src ∈ (next s (rowOf G C g j)).sources
          simpa [next, rowOf, e, a, b] using
            (List.mem_cons.mpr (Or.inl hs.symm) :
              some src ∈ project (readPin s a) (readPin s b) :: s.sources)
        · exact sources_keep _ _ _ (prevSrc (by omega))
  obtain ⟨all, held⟩ := inv C.gates.length le_rfl
  constructor
  · intro B good
    exact good.2 (some src) (held hglen)
  · intro t ht
    obtain ⟨hmem, hand, _⟩ := Finset.mem_filter.mp ht
    have kept : Kept G C (n+t) := by
      intro j hj he
      have e : j = t := by omega
      subst j
      have hor := (Finset.mem_filter.mp hj).2.1
      simp_all
    exact (all _ (Nat.add_lt_add_left (Finset.mem_range.mp hmem) n) kept).2

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
