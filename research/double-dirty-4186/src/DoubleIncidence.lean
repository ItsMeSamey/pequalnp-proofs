import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Incidence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

def Saving {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size + k ≤ C.size

theorem no_saving {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (least : IsLeastAO G C) : ¬ Saving G C 1 := by
  rintro ⟨D, ao, agree, size⟩
  have := least.2.2 D ao agree
  omega

theorem split_no_double_saving {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C split : Circuit} (least : IsLeastAO G C) (cost : split.size ≤ C.size + 1) :
    ¬ Saving G split 2 := by
  rintro ⟨D, ao, agree, size⟩
  have := least.2.2 D ao agree
  omega

def Fork {α : Type*} (step : α → α → Prop) (x : α) : Prop := ∃ a b, step x a ∧ step x b ∧ a ≠ b

theorem fork_of_incomparable {α : Type*} (step : α → α → Prop) {z a b : α}
    (za : Relation.ReflTransGen step z a) (zb : Relation.ReflTransGen step z b)
    (ab : ¬ Relation.ReflTransGen step a b) (ba : ¬ Relation.ReflTransGen step b a) :
    ∃ f, Relation.ReflTransGen step z f ∧ Fork step f ∧ Relation.TransGen step f a ∧ Relation.TransGen step f b := by
  induction za using Relation.ReflTransGen.head_induction_on with
  | refl => exact (ab zb).elim
  | @head z x zx xa ih =>
    rcases Relation.ReflTransGen.cases_head zb with eq | ⟨y, zy, yb⟩
    · subst b
      exact (ba (.head zx xa)).elim
    · by_cases same : x = y
      · subst y
        obtain ⟨f, xf, fork, fa, fb⟩ := ih yb
        exact ⟨f, .head zx xf, fork, fa, fb⟩
      · exact ⟨z, .refl, ⟨x,y,zx,zy,same⟩, Relation.TransGen.head' zx xa,
          Relation.TransGen.head' zy yb⟩

theorem no_common_ancestor {α : Type*} (step : α → α → Prop) {a b : α}
    (ha : Fork step a) (hb : Fork step b) (ne : a ≠ b)
    (antichain : ∀ {x y}, Fork step x → Fork step y → ¬ Relation.TransGen step x y) :
    ¬ ∃ z, Relation.ReflTransGen step z a ∧ Relation.ReflTransGen step z b := by
  rintro ⟨z,za,zb⟩
  have ab : ¬ Relation.ReflTransGen step a b := by
    intro path
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with h | h
    · exact ne h.symm
    · exact antichain ha hb h
  have ba : ¬ Relation.ReflTransGen step b a := by
    intro path
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with h | h
    · exact ne h
    · exact antichain hb ha h
  obtain ⟨f,_,hf,fa,_⟩ := fork_of_incomparable step za zb ab ba
  exact antichain hf ha fa

/-- After taking a direct reader of a branching wire, two distinct first terminal
roots would require another fork strictly downstream. -/
theorem unique_terminal_from_reader {α : Type*} (step : α → α → Prop)
    {x r a b : α} (fork : Fork step x) (read : step x r)
    (antichain : ∀ {s t}, Fork step s → Fork step t → ¬ Relation.TransGen step s t)
    (ra : Relation.ReflTransGen step r a) (rb : Relation.ReflTransGen step r b)
    (termA : ∀ v, ¬ step a v) (termB : ∀ v, ¬ step b v) : a = b := by
  by_contra ne
  have stop {v w : α} (h : ∀ u, ¬ step v u) (path : Relation.ReflTransGen step v w) : v = w := by
    rcases Relation.ReflTransGen.cases_head path with eq | ⟨u,vu,_⟩
    · exact eq
    · exact (h u vu).elim
  obtain ⟨f,rf,hf,_,_⟩ := fork_of_incomparable step ra rb (fun h => ne (stop termA h))
    (fun h => ne (stop termB h).symm)
  exact antichain fork hf (Relation.TransGen.head' read rf)

theorem root_count {α : Type*} [DecidableEq α] (step : α → α → Prop)
    {x : α} (fork : Fork step x) (R roots : Finset α) (small : R.card ≤ 2)
    (first : ∀ t ∈ roots, ∃ r ∈ R, step x r ∧ Relation.ReflTransGen step r t)
    (terminal : ∀ t ∈ roots, ∀ v, ¬ step t v)
    (antichain : ∀ {s t}, Fork step s → Fork step t → ¬ Relation.TransGen step s t) :
    roots.card ≤ 2 := by
  classical
  let chooseR (t : ↥roots) : ↥R := ⟨(first t.val t.property).choose, (first t.val t.property).choose_spec.1⟩
  have inj : Function.Injective chooseR := by
    intro a b eq
    have same := congrArg Subtype.val eq
    change (first a.val a.property).choose = (first b.val b.property).choose at same
    obtain ⟨_, ar, ap⟩ := (first a.val a.property).choose_spec
    obtain ⟨_, _, bp⟩ := (first b.val b.property).choose_spec
    rw [←same] at bp
    exact Subtype.ext (unique_terminal_from_reader step fork ar antichain ap bp
      (terminal a.val a.property) (terminal b.val b.property))
  have le : roots.card ≤ R.card := by simpa using Fintype.card_le_of_injective chooseR inj
  exact le.trans small

structure Leak (β : Type*) where
  arm : Bool
  external : β
  deriving DecidableEq

namespace Leak
variable {β ι : Type*} (p : ι → Leak β)

def roots [DecidableEq β] (l : Leak β) : Finset (Sum Bool β) :=
  {Sum.inl l.arm, Sum.inr l.external}

theorem intersects_iff [DecidableEq β] (l m : Leak β) :
    ((roots l) ∩ (roots m)).Nonempty ↔ l.arm = m.arm ∨ l.external = m.external := by
  classical
  constructor
  · rintro ⟨r,hr⟩
    obtain ⟨hl,hm⟩ := Finset.mem_inter.mp hr
    cases r <;> simp [roots] at hl hm <;> subst_vars <;> simp_all
  · rintro (h|h)
    · exact ⟨Sum.inl l.arm, by simp [roots,h]⟩
    · exact ⟨Sum.inr l.external, by simp [roots,h]⟩

theorem eq_of_labels [DecidableEq β] (distinct : Function.Injective (roots ∘ p))
    {i j : ι} (a : (p i).arm = (p j).arm) (b : (p i).external = (p j).external) : i = j := by
  apply distinct
  simp [Function.comp_def, roots, a, b]

theorem classify [DecidableEq β] (distinct : Function.Injective (roots ∘ p))
    (meeting : ∀ i j, i ≠ j → ((roots (p i)) ∩ (roots (p j))).Nonempty) :
    (∃ side : Bool, (∀ i, (p i).arm = side) ∧ Function.Injective (fun i => (p i).external)) ∨
    (∃ i j, (p i).arm ≠ (p j).arm ∧ (p i).external = (p j).external ∧
      ∀ k, k = i ∨ k = j) := by
  classical
  by_cases sides : ∃ i j, (p i).arm ≠ (p j).arm
  · obtain ⟨i,j,hij⟩ := sides
    have extEq {a b : ι} (ne : (p a).arm ≠ (p b).arm) : (p a).external = (p b).external := by
      have ab : a ≠ b := fun eq => ne (congrArg (fun k => (p k).arm) eq)
      exact ((intersects_iff (p a) (p b)).mp (meeting a b ab)).resolve_left ne
    have e := extEq hij
    refine Or.inr ⟨i,j,hij,e,?_⟩
    intro k
    by_cases ki : (p k).arm = (p i).arm
    · have kj : (p k).arm ≠ (p j).arm := fun h => hij (ki.symm.trans h)
      exact Or.inl (eq_of_labels p distinct ki ((extEq kj).trans e.symm))
    · have kj : (p k).arm = (p j).arm := by
        cases h : (p k).arm <;> cases h' : (p i).arm <;> cases h'' : (p j).arm <;> simp_all
      exact Or.inr (eq_of_labels p distinct kj ((extEq ki).trans e))
  · have same : ∀ i j, (p i).arm = (p j).arm := by simpa using sides
    by_cases inhabited : Nonempty ι
    · obtain ⟨i⟩ := inhabited
      exact Or.inl ⟨(p i).arm, fun j => same j i,
        fun a b he => eq_of_labels p distinct (same a b) he⟩
    · exact Or.inl ⟨false, fun i => (inhabited ⟨i⟩).elim,
        fun i _ _ => (inhabited ⟨i⟩).elim⟩

end Leak
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Incidence
