import ThreeNameGenericRoots
import ThreeNameGenericCarrier

namespace ThreeNameGenericHost
open ThreeNamePacked ThreeNameGenericTrail ThreeNamePinReduction
variable {O J : Type} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J] {w h : Nat}

def attachmentCheck (raw : O → BitVec w) (pins : List O) (table : ThreeNamePackedPins.Table w)
    (p : Frame J w) (roots : Finset J) (lift : O ↪ J) : Bool :=
  decide (∀ i : O, i ∉ pins → lift i ∈ p.ground ∧ lift i ∉ roots ∧
    p.words (lift i) = ThreeNamePackedPins.run table (raw i))

theorem rejects (raw : O → BitVec w) (pins : List O) (target a b : BitVec w)
    (table : ThreeNamePackedPins.Table w) (supports : Fin w → List O)
    (pinOK : ThreeNamePackedPins.check raw pins table supports = true)
    (p q : Frame J w) (i j k : J) (lift : O ↪ J)
    (initOK : ThreeNameGenericRoots.initialCheck p i j k target a b table = true)
    (attachOK : attachmentCheck raw pins table p {i,j,k} lift = true)
    (trail : Trail {i,j,k} p q) (terminal : Terminal q i j k h)
    (A : Finset O) (pinSub : pins.toFinset ⊆ A) :
    ¬ Exact (fun n => decode (raw n)) (ThreeNameGenericPositive.named target a b) A := by
  intro exactA
  let R := A \ pins.toFinset
  have un : pins.toFinset ∪ R = A := Finset.union_sdiff_of_subset pinSub
  have projExact := (ThreeNamePackedPins.checked_lift_iff raw pins table supports pinOK
    (ThreeNameGenericPositive.named target a b) R).mpr (un.symm ▸ exactA)
  obtain ⟨hij,hik,hjk,rootGround,indep,axis,names⟩ :=
    ThreeNameGenericRoots.rootFacts p i j k target a b table initOK
  unfold attachmentCheck at attachOK
  have attached := of_decide_eq_true attachOK
  have atom : ∀ n ∈ R \ pins.toFinset, lift n ∈ p.ground ∧ lift n ∉ ({i,j,k} : Finset J) ∧
      p.carrier.col (lift n) = decode (ThreeNamePackedPins.run table (raw n)) := by
    intro n hn
    have outside := (Finset.mem_sdiff.mp hn).2
    have ⟨g,d,eq⟩ := attached n (fun h => outside (List.mem_toFinset.mpr h))
    exact ⟨g,d,congrArg decode eq⟩
  have kill : ∀ n ∈ R ∩ pins.toFinset, decode (ThreeNamePackedPins.run table (raw n)) = 0 := by
    intro n hn
    have both := Finset.mem_inter.mp hn
    exact False.elim ((Finset.mem_sdiff.mp both.1).2 both.2)
  have witness := ThreeNameGenericCarrier.ordinary_support _ p.carrier {i,j,k} R pins.toFinset
    lift atom kill _ projExact axis names
  obtain ⟨s1,s2,s3⟩ := of_decide_eq_true terminal.starOK
  have binary (v : Vec w) : v+v=0 := by
    funext n
    exact (show ∀ z : ZMod 2, z+z=0 by decide) (v n)
  exact ThreeNameRejection.no_support p.carrier q.carrier i j k terminal.l terminal.r
    terminal.center hij hik hjk s1 s2 s3 binary trail.path terminal.kernel rootGround indep witness

#print axioms rejects
end ThreeNameGenericHost
