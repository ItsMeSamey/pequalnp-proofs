import T2CubeDeletion
namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds

structure Layers (n v w z : Nat) where
  first : Fin n → Finset (Fin v)
  second : Fin v → Finset (Fin w)
  third : Fin w → Finset (Fin z)
  firstTwo : ∀ i, (first i).card = 2
  secondTwo : ∀ i, (second i).card = 2
  thirdTwo : ∀ i, (third i).card = 2
  firstUsed : ∀ a, ∃ i, a ∈ first i
  secondUsed : ∀ b, ∃ a, b ∈ second a
  thirdUsed : ∀ c, ∃ b, c ∈ third b
  eight : ∀ i, ((first i).biUnion (fun a => (second a).biUnion third)).card = 8
  unique : Function.Injective (fun i => (first i).biUnion (fun a => (second a).biUnion third))

abbrev Bit := Option Nat
abbrev Build := StateM (List Gate)
def emit (n : Nat) (op : GateOp) (x y : Nat) : Build Bit := do
  let gates ← get
  set (gates ++ [⟨op,[x,y]⟩])
  return some (n + gates.length)

def disj (n : Nat) : Bit → Bit → Build Bit
  | none,y => pure y
  | x,none => pure x
  | some a,some b => emit n .or a b

def conj (n : Nat) : Bit → Bit → Build Bit
  | some a,some b => emit n .and a b
  | _,_ => pure none

def layer {p q : Nat} (n : Nat) (adj : Fin p → Finset (Fin q)) (src : List Bit) :
    Build (List Bit) :=
  (List.finRange q).mapM fun v =>
    (((List.finRange p).filter (fun i => decide (v ∈ adj i))).map
      (fun i => src.getD i.val none)).foldlM (disj n) none

def prefixStep (n : Nat) (old : List Bit) (x : Bit) : Build (List Bit) :=
  (List.range 9).mapM fun j => do
    let through ← if j = 0 then pure x else conj n x (old.getD (j-1) none)
    disj n (old.getD j none) through

def program {n v w z} (L : Layers n v w z) : Build Bit := do
  let a ← layer n L.first ((List.range n).map some)
  let b ← layer n L.second a
  let c ← layer n L.third b
  let out ← c.foldlM (prefixStep n) (List.replicate 9 none)
  return out.getD 8 none

def circuit {n v w z} (L : Layers n v w z) : Circuit :=
  let (out,gates) := (program L).run []
  ⟨gates,out.getD (n+gates.length)⟩
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
variable {n v w z : Nat}
def support (L : Layers n v w z) (i : Fin n) :=
  (L.first i).biUnion (fun a => (L.second a).biUnion L.third)

theorem threshold (L : Layers n v w z) (s : Finset (Fin n)) :
    9 ≤ (s.biUnion (support L)).card ↔ 2 ≤ s.card := by
  classical
  constructor
  · intro h
    by_contra! small
    by_cases emp : s = ∅
    · simp [emp] at h
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr emp
      have le : s.card ≤ 1 := by omega
      have eq : s = {i} := by
        ext a
        simp only [Finset.mem_singleton]
        exact ⟨fun ha => Finset.card_le_one.mp le a ha i hi,fun e => e ▸ hi⟩
      have card := L.eight i
      rw [eq,Finset.singleton_biUnion] at h
      change 9 ≤ ((support L) i).card at h
      change ((support L) i).card = 8 at card
      omega
  · intro h
    obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp h
    have eqs : ((support L) i).card = ((support L) j).card := (L.eight i).trans (L.eight j).symm
    have nsub : ¬ (support L) j ⊆ (support L) i := by
      intro sub
      exact ne (L.unique (Finset.eq_of_subset_of_card_le sub eqs.le).symm)
    obtain ⟨c,hc,hn⟩ := Finset.not_subset.mp nsub
    have subset : insert c ((support L) i) ⊆ s.biUnion (support L) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with e|ha
      · exact Finset.mem_biUnion.mpr ⟨j,hj,e ▸ hc⟩
      · exact Finset.mem_biUnion.mpr ⟨i,hi,ha⟩
    have bound := Finset.card_le_card subset
    have card : ((support L) i).card = 8 := L.eight i
    rwa [Finset.card_insert_of_notMem hn,card] at bound
end ThresholdThreeLayerUpper
