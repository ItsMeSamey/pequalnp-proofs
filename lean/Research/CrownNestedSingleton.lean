import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CrownNestedSingleton

/-- Until a second OR fires on a singleton, every true wire denotes one of three
ordered Boolean functions: the singleton literal, the first OR, or true. -/
theorem one_active_or_chain {X : Type*} (w : Nat → Set X) (p : X) (raw first : Set X)
    (hraw : raw ⊆ first) (stop : Nat)
    (step : ∀ i < stop, p ∈ w i → w i = raw ∨ w i = first ∨ w i = Set.univ ∨
      ∃ j < i, ∃ k < i, w i = w j ∩ w k) :
    ∀ i < stop, p ∈ w i → w i = raw ∨ w i = first ∨ w i = Set.univ := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hp
    rcases step i hi hp with e|e|e|⟨j,hj,k,hk,he⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · rw [he] at hp ⊢
      rcases ih j hj (hj.trans hi) hp.1 with e|e|e <;>
        rcases ih k hk (hk.trans hi) hp.2 with f|f|f <;>
        simp [e,f,Set.inter_eq_left.mpr hraw,Set.inter_eq_right.mpr hraw]

/-- A second OR with a first reader on the sibling must read the first OR on
its other input once repeated use of the raw wire and constant truth are excluded. -/
theorem second_parent {X : Type*} {w : Nat → Set X} {p : X} {r G : Set X}
    {wire g a : Nat} (chain : p ∈ w wire → w wire = r ∨ w wire = G ∨ w wire = Set.univ)
    (fires : p ∈ w wire) (raw : w a = r) (first : w g = G)
    (unique : ∀ j, w wire = w j → wire = j)
    (collisionFree : wire ≠ a) (notTop : w wire ≠ Set.univ) : wire = g := by
  rcases chain fires with e|e|e
  · exact (collisionFree (unique _ (e.trans raw.symm))).elim
  · exact unique _ (e.trans first.symm)
  · exact (notTop e).elim

/-- The sibling of a contaminating raw literal fires no OR. Both slots of its
diagonal are already occupied, and neither of those gates reads that sibling. -/
theorem contaminated_sibling {I G : Type*} [DecidableEq G] (fires : I → Finset G)
    (diag : Finset G) (j sibling : I) (g h : G) (distinct : g ≠ h)
    (jg : g ∈ fires j) (jh : h ∈ fires j) (includes : fires j ⊆ diag)
    (includesSibling : fires sibling ⊆ diag) (cap : diag.card ≤ 2)
    (sg : g ∉ fires sibling) (sh : h ∉ fires sibling) : fires sibling = ∅ := by
  classical
  have sub : {g,h} ⊆ diag := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl|hh
    · exact includes jg
    · exact (Finset.mem_singleton.mp hh) ▸ includes jh
  have eq : ({g,h} : Finset G) = diag := Finset.eq_of_subset_of_card_le sub (by simpa [distinct] using cap)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have mem := includesSibling ht
  rw [←eq] at mem
  simp only [Finset.mem_insert,Finset.mem_singleton] at mem
  rcases mem with rfl|rfl
  · exact sg ht
  · exact sh ht

/-- A contaminating raw index identifies the ordered pair of ORs it fires. -/
theorem ordered_pair_unique {g h g' h' : Nat} (lt : g < h) (lt' : g' < h')
    (eq : ({g,h} : Finset Nat) = {g',h'}) : g = g' ∧ h = h' := by
  have hg : g ∈ ({g',h'} : Finset Nat) := eq ▸ Finset.mem_insert_self ..
  have hh : h ∈ ({g',h'} : Finset Nat) := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hg hh
  omega

/-- With the contaminating literal fixed, the earlier singleton is determined
by the two distinct raw readers of its first OR. -/
theorem contaminated_injective {I N : Type*} [DecidableEq I] (row extra : N → I)
    (g h : N → Nat) (fires : I → Finset Nat) (reads : Nat → Finset I)
    (order : ∀ n, g n < h n) (separate : ∀ n, row n ≠ extra n)
    (active : ∀ n, fires (extra n) = {g n,h n})
    (parents : ∀ n, reads (g n) = {row n,extra n})
    (rowUnique : Function.Injective row) : Function.Injective extra := by
  intro a b hab
  have gate := (ordered_pair_unique (order a) (order b)
    ((active a).symm.trans ((congrArg fires hab).trans (active b)))).1
  apply rowUnique
  have mem : row a ∈ reads (g a) := by simp [parents]
  rw [gate,parents] at mem
  rcases Finset.mem_insert.mp mem with e|e
  · exact e
  · exact (separate a ((Finset.mem_singleton.mp e).trans hab.symm)).elim

/-- For an AND with zero baseline false, choose a zero-false parent.
The singleton signature of the AND is contained in that parent's signature.
Induction then localizes every relevant wire, including uncharged ANDs. -/
theorem clean_wire_isolation {I : Type*} [DecidableEq I] (sig : Nat → Finset I)
    (off : Nat → Prop) (a b : I)
    (step : ∀ w, off w → a ∈ sig w → sig w ⊆ {a,b} ∨
      ∃ p < w, off p ∧ sig w ⊆ sig p) :
    ∀ w, off w → a ∈ sig w → sig w ⊆ {a,b} := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro base fired
    rcases step w base fired with hs|⟨p,hp,base',hs⟩
    · exact hs
    · exact hs.trans (ih p hp base' (hs fired))

/-- A clean nest's early singleton can share a wire only with its sibling.
Scaled weights at most two on that pair preserve the capacity of four. -/
theorem clean_reweight_cap {I : Type*} [DecidableEq I] (S clean : Finset I)
    (sibling : I → I) (old new : I → Nat) (oldCap : ∑ i ∈ S, old i ≤ 4)
    (untouched : ∀ i ∈ S, i ∉ clean → new i = old i)
    (isolate : ∀ i ∈ S, i ∈ clean → S ⊆ {i,sibling i})
    (newBound : ∀ i ∈ S, i ∈ clean → new i ≤ 2 ∧ new (sibling i) ≤ 2) :
    ∑ i ∈ S, new i ≤ 4 := by
  classical
  by_cases hit : ∃ i ∈ S, i ∈ clean
  · obtain ⟨i,hi,hc⟩ := hit
    have H := newBound i hi hc
    calc
      ∑ j ∈ S, new j ≤ ∑ j ∈ ({i,sibling i} : Finset I), new j :=
        Finset.sum_le_sum_of_subset (isolate i hi hc)
      _ ≤ 4 := by
        by_cases e : i = sibling i
        · have same : ({i,sibling i} : Finset I) = {i} := by rw [← e]; simp
          rw [same,Finset.sum_singleton]
          omega
        · rw [Finset.sum_insert (by simpa using e),Finset.sum_singleton]
          omega
  · convert oldCap using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact untouched i hi (fun hc => hit ⟨i,hi,hc⟩)

/-- A contaminated literal and its silent sibling determine a unique diagonal
label. Distinct contaminants cannot map to the same zero-sibling label. -/
theorem contaminated_label_injective {N I L G : Type*} (extra : N → I) (sibling : I → I)
    (label : I → L) (fires : I → Finset G) (inj : Function.Injective extra)
    (fibers : ∀ a b, label a = label b → a = b ∨ a = sibling b)
    (hot : ∀ n, (fires (extra n)).Nonempty) (silent : ∀ n, fires (sibling (extra n)) = ∅) :
    Function.Injective (fun n => label (extra n)) := by
  intro u v eq
  rcases fibers _ _ eq with e|e
  · exact inj e
  · have both := hot u
    rw [e,silent] at both
    exact (Finset.not_nonempty_empty both).elim

end CrownNestedSingleton
