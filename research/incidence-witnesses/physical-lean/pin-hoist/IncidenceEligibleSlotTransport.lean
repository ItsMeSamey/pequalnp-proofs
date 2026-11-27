import IncidenceHoistSingleton
import IncidenceHoistSlotMap
import IncidencePinHoistSparse
namespace IncidenceEligibleSlotTransport
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow IncidenceHoistCompile
open IncidenceHoistWalk IncidenceHoistSingleton IncidenceHoistSlotMap IncidenceLineRoutedSlots
variable {n : Nat} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]
variable (degree : ∀ l,Fintype.card {p // I p l}=401+1)
variable (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
variable (pos : flags C I) (neg : negatives C I n 2)

include degree unique pos neg in
theorem retained {x p : Fin n} {g : Fin C.size} (h : eligible C I x g p) :
    select C true g.val=none := by
  cases eq : select C true g.val with
  | none => rfl
  | some b =>
    obtain ⟨_,_,_,⟨a,_,_,ha⟩,⟨d,_,_,hd⟩⟩ := h
    cases b
    · exact (IncidencePinHoistSparse.pure_point C I degree unique pos neg eq a ha).elim
    · exact (IncidencePinHoistSparse.pure_point C I degree unique pos neg eq d hd).elim

def NamedGate := {g : Fin C.size // ∃ x p, eligible C I x g p}

def mapping : NamedGate C I ↪ Fin (circuit C (select C true)).size :=
  ⟨fun g => embedding C (select C true) ⟨g.val,by
      obtain ⟨x,p,h⟩ := g.property
      exact retained C I degree unique pos neg h⟩,by
    intro a b eq
    exact Subtype.ext (congrArg (fun u : {g : Fin C.size // select C true g.val=none} => u.val) ((embedding C (select C true)).injective eq))⟩

include degree unique pos neg in
theorem hit_equivalence (g : NamedGate C I) (p : Fin n) :
    let D := circuit C (select C true)
    let newG := mapping C I degree unique pos neg g
    (hit D (n+n+newG.val) p ↔ hit C (n+n+g.val.val) p) ∧
      (hit D (D.code newG).left p ↔ hit C (C.code g.val).left p) ∧
      (hit D (D.code newG).right p ↔ hit C (C.code g.val).right p) := by
  let sel := select C true
  obtain ⟨x,a,h⟩ := g.property
  have kept := retained C I degree unique pos neg h
  have join (j : Nat) (_ : j<C.size) (b : Bool) (hh : sel j=some b) : (C.code j).op=.join :=
    (IncidencePinHoistSparse.selected_shield C I neg hh).choose_spec.1
  let z := witness false p
  have quiet : Quiet C sel z := fun _ _ _ h => IncidencePinHoistSparse.pure_point C I degree unique pos neg h p
  have ⟨l,r⟩ := C.earlier _ g.val.isLt
  have hs := agrees C sel z join quiet (n+n+g.val.val) (by have := g.val.isLt; omega)
  rw [kept_ref (n+n) C.size C.code sel _ g.val.isLt kept] at hs
  have gate := physical_gate C sel _ g.val.isLt kept
  change _ ∧ (hit _ ((circuit C sel).code (rank (n+n) C.code sel g.val.val)).left _ ↔ _) ∧
    (hit _ ((circuit C sel).code (rank (n+n) C.code sel g.val.val)).right _ ↔ _)
  rw [gate]
  exact ⟨hs,agrees_prefix C sel z join quiet _ _ g.val.isLt.le l,
    agrees_prefix C sel z join quiet _ _ g.val.isLt.le r⟩

include degree unique pos neg in
theorem preserved (g : NamedGate C I) (x p : Fin n) :
    eligible (circuit C (select C true)) I x (mapping C I degree unique pos neg g) p ↔
      eligible C I x g.val p := by
  have kept : select C true g.val.val=none := by
    obtain ⟨u,v,ok⟩ := g.property
    exact retained C I degree unique pos neg ok
  have op := congrArg Gate.op (physical_gate C (select C true) _ g.val.isLt kept)
  change ((circuit C (select C true)).code (mapping C I degree unique pos neg g)).op=(C.code g.val).op at op
  constructor
  · rintro ⟨og,inc,hp,⟨a,ia,ap,ha⟩,⟨b,ib,bp,hb⟩⟩
    exact ⟨op ▸ og,inc,(hit_equivalence C I degree unique pos neg g p).1.mp hp,
      ⟨a,ia,ap,(hit_equivalence C I degree unique pos neg g a).2.1.mp ha⟩,
      ⟨b,ib,bp,(hit_equivalence C I degree unique pos neg g b).2.2.mp hb⟩⟩
  · rintro ⟨og,inc,hp,⟨a,ia,ap,ha⟩,⟨b,ib,bp,hb⟩⟩
    exact ⟨op.symm ▸ og,inc,(hit_equivalence C I degree unique pos neg g p).1.mpr hp,
      ⟨a,ia,ap,(hit_equivalence C I degree unique pos neg g a).2.1.mpr ha⟩,
      ⟨b,ib,bp,(hit_equivalence C I degree unique pos neg g b).2.2.mpr hb⟩⟩

#print axioms mapping
#print axioms preserved
end IncidenceEligibleSlotTransport
