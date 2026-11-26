import ThresholdOrPhysicalBook
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction

namespace ThresholdRemoteAnchor
abbrev Row (v : Nat) := Fin v → Bool

def setBit {v : Nat} (x : Row v) (p : Fin v) (b : Bool) : Row v :=
  fun i => if i=p then b else x i

def essential {v : Nat} (f : Row v → Bool) (p : Fin v) : Prop :=
  ∃ x : Row v, x p=false ∧ f x ≠ f (setBit x p true)

/-- One endpoint can be charged at a remote anchor. No prescribed value
of the intermediate row is needed: it may be outside the edge-row image. -/
theorem anchor_endpoint {v : Nat} (f : Row v → Bool) (x : Row v) (a b : Fin v)
    (ab : a≠b) (xa : x a=false) (xb : x b=false)
    (fl : f x=false) (fr : f (setBit (setBit x a true) b true)=true) :
    essential f a ∨ essential f b := by
  cases mid : f (setBit x a true) with
  | true => exact Or.inl ⟨x,xa,by simp [fl,mid]⟩
  | false =>
    refine Or.inr ⟨setBit x a true,?_,by simp [mid,fr]⟩
    simp [setBit,Ne.symm ab,xb]

/-- Encodes exactly the three semantic witnesses needed to charge an
interior-vertex restriction. The retaining row can be reused through all
steps that avoid the central star. -/
def Witness {v : Nat} (f : Row v → Bool) (p : Fin v) : Prop :=
  essential f p ∧ ∃ z : Row v, z p=false ∧ f z=true

theorem interior {v : Nat} (f : Row v → Bool) (p : Fin v) (one two star : Row v)
    (off : one p=false) (pair : setBit one p true=two)
    (singleReject : f one=false) (pairAccept : f two=true)
    (starOff : star p=false) (starAccept : f star=true) :
    Witness f p := by
  exact ⟨⟨one,off,by simp [pair,singleReject,pairAccept]⟩,star,starOff,starAccept⟩

/-- Under any peels respecting the fixed central-star positive, one of
a,b remains eligible for a charged deletion and the other can be deleted
for free. -/
theorem anchor_witness {v : Nat} (f : Row v → Bool) (x z : Row v) (a b : Fin v)
    (ab : a≠b) (xa : x a=false) (xb : x b=false)
    (fl : f x=false) (fr : f (setBit (setBit x a true) b true)=true)
    (za : z a=false) (zb : z b=false) (positive : f z=true) :
    Witness f a ∨ Witness f b := by
  exact (anchor_endpoint f x a b ab xa xb fl fr).elim
    (fun e => Or.inl ⟨e,z,za,positive⟩) (fun e => Or.inr ⟨e,z,zb,positive⟩)

end ThresholdRemoteAnchor
