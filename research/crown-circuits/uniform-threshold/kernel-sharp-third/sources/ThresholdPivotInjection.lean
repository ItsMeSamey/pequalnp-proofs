import ThresholdPivotCold
import ReadOnceLCA
namespace ThresholdPivotStar
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition T2SoleOrSplice
open ThresholdEffectiveColumns ThresholdPhysicalFirstCut
variable {C : Circuit} {n k : Nat} (L : Layout C n) (D : Star C n k L) (M : LexMinimum n C)

def bits (x y : Fin k) (a b : Bool) : Finset (Fin k) :=
  (if a then {x} else ∅) ∪ (if b then {y} else ∅)

/-- The sole remaining physical formula-extraction interface.  The two fixed
environments correspond to zero or one third bit. -/
def PairContexts : Prop := ∀ x y z : Fin k, x≠y → z≠x → z≠y →
  first L D M x=first L D M y →
  ∃ (t : ReadOnceLCA.Formula (Bool ⊕ Fin k ⊕ Id C))
    (a b : (Bool ⊕ Fin k ⊕ Id C) → Bool),
    t.xCount≤1 ∧ t.yCount≤1 ∧
    (∀ p q,t.eval a p q=changed L D (bits x y p q) (first L D M x)) ∧
    (∀ p q,t.eval b p q=changed L D (insert z (bits x y p q)) (first L D M x))

private theorem unary_id (f : Bool → Bool) (lo hi : Bool)
    (fl : f lo=false) (fh : f hi=true) (mono : lo=true → hi=true) : ∀ b,f b=b := by
  cases lo <;> cases hi <;> cases h : f false <;> cases j : f true <;> simp_all

theorem injection (ctx : PairContexts L D M) (hk : 3≤k)
    (twice : ∀ w : Fin n,(readers C w.val).length=2) (out : Id C) (obs : C.output=n+out.val) :
    Function.Injective (first L D M) := by
  classical
  intro x y same
  by_contra ne
  let rest := (Finset.univ : Finset (Fin k)) \ {x,y}
  have existsZ : rest.Nonempty := by
    apply Finset.card_pos.mp
    have sub : ({x,y} : Finset (Fin k))⊆Finset.univ := Finset.subset_univ _
    simp [rest,Finset.card_sdiff_of_subset sub,ne]; omega
  obtain ⟨z,hz⟩ := existsZ
  have zx : z≠x := by intro eq; subst z; simp [rest] at hz
  have zy : z≠y := by intro eq; subst z; simp [rest] at hz
  let d := first L D M x
  obtain ⟨t,a,b,tx,ty,zero,one⟩ := ctx x y z ne zx zy same
  have owned : ∀ j∈({x,y} : Finset _),first L D M j=d := by
    intro j hj; rcases Finset.mem_insert.mp hj with rfl|h
    · rfl
    · obtain rfl := Finset.mem_singleton.mp h; exact same.symm
  have truth := threshold L D M twice x out obs
  have decode (base : Finset (Fin k)) (off : (changed L D base out)=false)
      (on : changed L D (base∪{x,y}) out=true) :
      ∀ u⊆({x,y} : Finset _),changed L D (base∪u) d=changed L D (base∪u) out := by
    obtain ⟨f,hf⟩ := fiber_unary L M {D.pivot,D.shared} D.privatePin d out obs base {x,y} owned
    change ∀ e⊆({x,y} : Finset _), changed L D (base∪e) out=f (changed L D (base∪e) d) at hf
    have f0 := hf ∅ (Finset.empty_subset _)
    simp only [Finset.union_empty,off] at f0
    have f1 := hf {x,y} (Finset.Subset.rfl)
    rw [on] at f1
    have mono := monotone L (patch {D.pivot,D.shared} D.privatePin) base (base∪{x,y})
      Finset.subset_union_left d
    have id := unary_id f _ _ f0.symm f1.symm mono
    intro u hu
    simpa [id] using (hf u hu).symm
  have off0 : changed L D ∅ out=false := Bool.eq_false_iff.mpr (fun h => by simpa using (truth ∅).mp h)
  have off1 : changed L D {z} out=false := Bool.eq_false_iff.mpr (fun h => by simpa using (truth {z}).mp h)
  have on0 : changed L D (∅∪{x,y}) out=true := (truth _).mpr (by simp [ne])
  have on1 : changed L D ({z}∪{x,y}) out=true := (truth _).mpr (by
    have two : 2≤({x,y} : Finset (Fin k)).card := by simp [ne]
    exact two.trans (Finset.card_le_card Finset.subset_union_right))
  have subs (p q : Bool) : bits x y p q⊆{x,y} := by cases p <;> cases q <;> simp [bits]
  apply ReadOnceLCA.no_and_or_of_occurrences t tx ty a b
  · intro p q
    rw [zero]
    have result := decode ∅ off0 on0 _ (subs p q)
    simp only [Finset.empty_union] at result
    rw [result]
    apply Bool.eq_iff_iff.mpr
    rw [truth]
    cases p <;> cases q <;> simp [bits,ne]
  · intro p q
    rw [one]
    have result := decode {z} off1 on1 _ (subs p q)
    simp only [Finset.singleton_union] at result
    rw [result]
    apply Bool.eq_iff_iff.mpr
    rw [truth]
    cases p <;> cases q <;> simp [bits,ne,zx,zy]

theorem cold_multiplicity (ctx : PairContexts L D M)
    (twice : ∀ w : Fin n,(readers C w.val).length=2) (out : Id C) (obs : C.output=n+out.val) :
    (cold L D M).card≤2 := by
  have bound := cold_quota L D M out obs twice (fun hk => injection L D M ctx hk twice out obs)
  split at bound <;> omega

/-- Convert the fixed ordered opposite-row/shared-receiver key to its quota.
The candidate map is only required to be injective on that one fiber. -/
theorem cold_key {P : Type*} [DecidableEq P] (pool : Finset P) (row : P → Fin k)
    (incl : ∀ a∈pool,row a∈cold L D M) (distinct : Set.InjOn row (pool : Set P))
    (ctx : PairContexts L D M)
    (twice : ∀ w : Fin n,(readers C w.val).length=2) (out : Id C) (obs : C.output=n+out.val) :
    pool.card≤2 := by
  have a : pool.image row⊆cold L D M := by
    intro x hx; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx; exact incl _ hi
  have b := Finset.card_le_card a
  rw [Finset.card_image_of_injOn distinct] at b
  exact b.trans (cold_multiplicity L D M ctx twice out obs)
end ThresholdPivotStar
