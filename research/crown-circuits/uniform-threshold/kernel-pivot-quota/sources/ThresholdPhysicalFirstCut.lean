import ThresholdOverrideCut
import ThresholdEffectiveColumns
namespace ThresholdPhysicalFirstCut
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins T2SoleOrSplice
open ThresholdEffectiveColumns ThresholdFirstMarkCut ThresholdOverrideCut
variable {C : Circuit} {n k : Nat} (L : Layout C n)

noncomputable def partition (M : LexMinimum n C) : Partition L where
  marked := boundary (C:=C) (n:=n)
  first := column L M
  onMark := column_of_boundary L M
  follows := fun j i b off edge => column_of_feed L M j (i,b) off edge

/-- Forcing both operands to true forces either monotone gate. Each fresh
variable receives exactly its designated physical occurrence. -/
noncomputable def patch (forced : Finset (Id C)) (socket : Fin k → Pin C)
    (p : Pin C) : Option (Bool ⊕ Fin k) := by
  classical
  exact if p.1∈forced then some (.inl true)
    else if h : ∃ x, socket x=p then some (.inr h.choose) else none

theorem fresh_route (M : LexMinimum n C) (forced : Finset (Id C)) (socket : Fin k → Pin C)
    (p : Pin C) (x : Fin k) (hit : patch forced socket p=some (.inr x)) :
    column L M (socket x).1=column L M p.1 := by
  classical
  unfold patch at hit
  split at hit
  · simp at hit
  · split at hit
    next ex =>
      have eq : ex.choose=x := by simpa using hit
      exact congrArg (fun j : Pin C => column L M j.1) (eq ▸ ex.choose_spec)
    next => contradiction

theorem physical_unary (M : LexMinimum n C) (forced : Finset (Id C)) (socket : Fin k → Pin C)
    (u out : Id C) (observed : C.output=n+out.val) (family : Finset (Fin k) → Prop)
    (fixed : ∀ s, family s → ∀ t, family t → ∀ x,
      column L M (socket x).1≠u → (x∈s ↔ x∈t)) :
    ∃ d : Bool → Bool, ∀ s, family s →
      ThresholdOverrideCut.eval L (patch forced socket) s out=
        d (ThresholdOverrideCut.eval L (patch forced socket) s u) :=
  ThresholdOverrideCut.unary L (patch forced socket) (partition L M)
    (fun x => column L M (socket x).1) (fresh_route L M forced socket)
    u out (Or.inl observed) family fixed
/-- All assignments of one mark's variables over a fixed context share a
single unary decoder. The context may include a third active variable. -/
theorem fiber_unary (M : LexMinimum n C) (forced : Finset (Id C)) (socket : Fin k → Pin C)
    (u out : Id C) (observed : C.output=n+out.val) (base free : Finset (Fin k))
    (owned : ∀ x∈free, column L M (socket x).1=u) :
    ∃ d : Bool → Bool, ∀ extra⊆free,
      ThresholdOverrideCut.eval L (patch forced socket) (base∪extra) out=
        d (ThresholdOverrideCut.eval L (patch forced socket) (base∪extra) u) := by
  let family : Finset (Fin k) → Prop := fun s => ∃ extra⊆free,s=base∪extra
  obtain ⟨d,hd⟩ := physical_unary L M forced socket u out observed family (by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ x outside
    have na : x∉a := fun h => outside (owned x (ha h))
    have nb : x∉b := fun h => outside (owned x (hb h))
    simp [na,nb])
  exact ⟨d,fun extra he => hd _ ⟨extra,he,rfl⟩⟩
end ThresholdPhysicalFirstCut
