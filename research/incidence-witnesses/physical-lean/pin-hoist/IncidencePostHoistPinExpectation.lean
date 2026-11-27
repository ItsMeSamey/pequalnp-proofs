import IncidenceEligibleSlotTransport
import IncidencePhysicalPinExpectation
namespace IncidencePostHoistPinExpectation
open scoped BigOperators
open SparseIncidence IncidenceStartNormalization IncidenceLineRoutedSlots IncidenceEligiblePin
open IncidenceActualPinFamily IncidenceLinePinBooking IncidenceHoistCompile IncidenceHoistWalk
open IncidenceEligibleSlotTransport IncidencePhysicalPinExpectation

theorem expected {n : Nat} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]
    (degree : ∀ l,Fintype.card {p // I p l}=401+1)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l) (hn : n=401^2+401+1)
    (pos : flags C I) (neg : negatives C I n 2) (owner : Fin C.size→Fin n)
    (book : Fin C.size→Finset (Fin n)) (ok : ∀g,∀p∈book g,eligible C I (owner g) g p) (j : Nat) :
    (401*Nat.choose 401 j)*(∑g,(book g).card) ≤
      ∑run∈sample I j,(forced (circuit C (select C true)) run.2).card := by
  classical
  let D := circuit C (select C true)
  let e := mapping C I degree unique pos neg
  let pulled (run : Fin n × Finset (Fin n)) := Finset.univ.filter (fun g : Fin C.size =>
    ∃ h : ∃ x p, eligible C I x g p, e ⟨g,h⟩∈forced D run.2)
  have bounded (run : Fin n × Finset (Fin n)) : (pulled run).card ≤ (forced D run.2).card := by
    let witness (u : ↥(pulled run)) := (Finset.mem_filter.mp u.property).2
    let f (u : ↥(pulled run)) : ↥(forced D run.2) :=
      ⟨e ⟨u.val,(witness u).choose⟩,(witness u).choose_spec⟩
    have inj : Function.Injective f := by
      intro a b eq
      apply Subtype.ext
      exact congrArg (fun u : NamedGate C I => u.val) (e.injective (congrArg (fun v : ↥(forced D run.2) => v.val) eq))
    simpa using Fintype.card_le_of_injective f inj
  apply le_trans _ (Finset.sum_le_sum (fun r _ => bounded r))
  apply finite_book (sample I j) Finset.univ book (fun g p=>event I (owner g) p j) pulled
  · intro g _ p hp
    exact (event_card I degree unique (by decide) hn (ok g p hp).2.1 j).ge
  · intro g _
    exact different_points I unique (owner g) (book g) (fun p h=>(ok g p h).2.1) j
  · intro g _ p hp run ev
    have old := ok g p hp
    let h : ∃ x p, eligible C I x g p := ⟨owner g,p,old⟩
    let id : NamedGate C I := ⟨g,h⟩
    have newOk := (preserved C I degree unique pos neg id (owner g) p).mpr old
    obtain ⟨diff,_,chosen,sub,sampled⟩ := event_spec I ev
    have ⟨high,⟨a,outA,_,ha⟩,⟨b,outB,_,hb⟩⟩ := pin_forces I unique D (e id)
      (owner g) run.1 p diff run.2 (fun i hi=>(Finset.mem_filter.mp (sub hi)).2) chosen newOk
    exact ⟨sampled,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,newOk.1,high,⟨a,outA,ha⟩,⟨b,outB,hb⟩⟩⟩⟩

#print axioms expected
end IncidencePostHoistPinExpectation
