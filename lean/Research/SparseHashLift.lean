import Mathlib.Data.Finset.Card

namespace SparseHashLift

variable {A L H C : Type*} [DecidableEq C]

def bucket (h : L → C) (c : C) (B : Finset L) : Finset L :=
  B.filter (fun l => h l = c)

def separator (F : A → Finset L → Prop) (family : Finset H) (color : H → L → C)
    (x : A) (B : Finset L) : Prop :=
  ∀ h ∈ family, ∃ c, F x (bucket (color h) c B)

/-- For a coloring injective on B, each occupied bucket is a singleton. -/
theorem singleton_bucket {h : L → C} {B : Finset L} (inj : Set.InjOn h B)
    {c : C} {l : L} (mem : l ∈ bucket h c B) : bucket h c B = {l} := by
  obtain ⟨lB,lc⟩ := Finset.mem_filter.mp mem
  ext j
  constructor
  · intro hj
    obtain ⟨jB,jc⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_singleton.mpr (inj jB lB (jc.trans lc.symm))
  · intro hj
    simpa only [Finset.mem_singleton.mp hj] using mem

/-- Any monotone circuit exact on empty and singleton masks extends to k-sparse masks
by a finite family of colorings perfect on every such mask. -/
theorem exact_on_sparse (F : A → Finset L → Prop) (R : A → L → Prop)
    (mono : ∀ x ⦃B B' : Finset L⦄, B ⊆ B' → F x B → F x B')
    (empty : ∀ x, ¬ F x ∅) (single : ∀ x l, F x {l} ↔ R x l)
    (family : Finset H) (color : H → L → C) (k : ℕ)
    (perfect : ∀ B : Finset L, B.card ≤ k → ∃ h ∈ family, Set.InjOn (color h) B)
    (x : A) (B : Finset L) (small : B.card ≤ k) :
    separator F family color x B ↔ ∃ l ∈ B, R x l := by
  constructor
  · intro accept
    obtain ⟨h,hm,inj⟩ := perfect B small
    obtain ⟨c,hc⟩ := accept h hm
    by_cases occupied : (bucket (color h) c B).Nonempty
    · obtain ⟨l,hl⟩ := occupied
      have b := (Finset.mem_filter.mp hl).1
      rw [singleton_bucket inj hl] at hc
      exact ⟨l,b,(single x l).mp hc⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp occupied] at hc
      exact False.elim (empty x hc)
  · rintro ⟨l,hl,yes⟩ h _
    refine ⟨color h l,mono x ?_ ((single x l).mpr yes)⟩
    simpa [bucket] using hl

theorem separator_mono (F : A → Finset L → Prop)
    (mono : ∀ x ⦃B B' : Finset L⦄, B ⊆ B' → F x B → F x B')
    (family : Finset H) (color : H → L → C) (x : A) {B B' : Finset L} (sub : B ⊆ B') :
    separator F family color x B → separator F family color x B' := by
  intro accept h hin
  obtain ⟨c,hc⟩ := accept h hin
  refine ⟨c,mono x ?_ hc⟩
  exact fun l hl => Finset.mem_filter.mpr ⟨sub (Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl).2⟩

theorem bounded_load_lift (F : A → Finset L → Prop) (R : A → L → Prop)
    (mono : ∀ x ⦃B B' : Finset L⦄, B ⊆ B' → F x B → F x B')
    (cap : ℕ) (cap_pos : 1 ≤ cap)
    (base : ∀ x B, B.card ≤ cap → (F x B ↔ ∃ l ∈ B, R x l))
    (family : Finset H) (color : H → L → C) (k : ℕ)
    (balanced : ∀ B : Finset L, B.card ≤ k → ∃ h ∈ family, ∀ c, (bucket (color h) c B).card ≤ cap)
    (x : A) (B : Finset L) (small : B.card ≤ k) :
    separator F family color x B ↔ ∃ l ∈ B, R x l := by
  constructor
  · intro accept
    obtain ⟨h,hm,bound⟩ := balanced B small
    obtain ⟨c,hc⟩ := accept h hm
    obtain ⟨l,hl,yes⟩ := (base x _ (bound c)).mp hc
    exact ⟨l,(Finset.mem_filter.mp hl).1,yes⟩
  · rintro ⟨l,hl,yes⟩ h _
    have start := (base x {l} (by simpa using cap_pos)).mpr ⟨l,by simp,yes⟩
    refine ⟨color h l,mono x ?_ start⟩
    simpa [bucket] using hl

end SparseHashLift
