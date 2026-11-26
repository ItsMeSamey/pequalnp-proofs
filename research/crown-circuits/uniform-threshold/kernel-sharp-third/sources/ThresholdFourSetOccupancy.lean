import ThresholdSharpCodegrees
namespace ThresholdFourSetOccupancy

/-- The three complementary pairs of edges in a four-set. -/
structure Quad where
  ab : Bool
  cd : Bool
  ac : Bool
  bd : Bool
  ad : Bool
  bc : Bool

def ofGraph {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d : V) : Quad :=
  ⟨decide (G.Adj a b),decide (G.Adj c d),decide (G.Adj a c),decide (G.Adj b d),
   decide (G.Adj a d),decide (G.Adj b c)⟩

def occupancy (x : Quad) : Nat :=
  (x.ab && x.cd).toNat + (x.ac && x.bd).toNat + (x.ad && x.bc).toNat

def C₁ (x : Quad) := x.ac && x.bd && x.ad && x.bc
def C₂ (x : Quad) := x.ab && x.cd && x.ad && x.bc
def C₃ (x : Quad) := x.ab && x.cd && x.ac && x.bd

def diagonals (x : Quad) : Nat := 2*((C₁ x).toNat+(C₂ x).toNat+(C₃ x).toNat)
def nonedge (x : Quad) : Nat :=
  (C₁ x).toNat*((!x.ab).toNat+(!x.cd).toNat)+
  (C₂ x).toNat*((!x.ac).toNat+(!x.bd).toNat)+
  (C₃ x).toNat*((!x.ad).toNat+(!x.bc).toNat)

theorem identities (x : Quad) :
    diagonals x=2*(occupancy x).choose 2 ∧ diagonals x≤3*(occupancy x-1) ∧
      nonedge x≤2*(occupancy x-1) := by
  obtain ⟨a,b,c,d,e,f⟩ := x
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem totals {I : Type*} (boxes : Finset I) (x : I → Quad) :
    (∑ i ∈ boxes, diagonals (x i))≤3*∑ i ∈ boxes, (occupancy (x i)-1) ∧
    (∑ i ∈ boxes, nonedge (x i))≤2*∑ i ∈ boxes, (occupancy (x i)-1) := by
  constructor
  · simpa only [Finset.mul_sum] using Finset.sum_le_sum
      (fun i (_ : i ∈ boxes) => (identities (x i)).2.1)
  · simpa only [Finset.mul_sum] using Finset.sum_le_sum
      (fun i (_ : i ∈ boxes) => (identities (x i)).2.2)
end ThresholdFourSetOccupancy
