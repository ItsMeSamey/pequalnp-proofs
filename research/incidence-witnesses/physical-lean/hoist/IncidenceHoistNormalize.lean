import IncidenceHoistEndpoint
import IncidenceHoistStage
import IncidenceHoistSensitive
import HoistPhysicalPorts
namespace IncidenceHoistNormalize
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow IncidenceHoistWalk
open IncidenceHoistEndpoint IncidenceHoistReaders IncidenceHoistPorts IncidenceHoistCompile
open IncidenceHoistPrefix IncidenceHoistStage HoistPhysicalPorts

def meetWeight (op : Op) : ℕ := if op=.meet then 1 else 0

private theorem meet_hit {n} (C : Circuit n) (w j : ℕ) (b : Bool)
    (js : j<C.size) (read : operand (C.code j) b=w) (op : (C.code j).op=.meet) :
    0<count meetWeight w (circuitCode C) := by
  refine (circuit_count_pos C meetWeight w).mpr ⟨j,js,by simp [meetWeight,op],?_⟩
  cases b
  · exact Or.inr read
  · exact Or.inl read

private theorem private_meet {n} (C : Circuit n) (w : ℕ) (one : uses C w=1)
    (hit : 0<count meetWeight w (circuitCode C)) :
    ∀ j<C.size, (C.code j).left=w ∨ (C.code j).right=w → (C.code j).op=.meet := by
  obtain ⟨k,hk,weight,port⟩ := (circuit_count_pos C meetWeight w).mp hit
  have op : (C.code k).op=.meet := by by_contra bad; simp [meetWeight,bad] at weight
  obtain ⟨cut,b,_,_,_,uniq⟩ := unique_reader C w one
  have e : k=cut := port.elim (fun x => (uniq k hk true x).1) (fun x => (uniq k hk false x).1)
  intro j hj read
  have eq : j=cut := read.elim (fun x => (uniq j hj true x).1) (fun x => (uniq j hj false x).1)
  exact (e.trans eq.symm) ▸ op

variable {n : ℕ} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]
variable (hn : n=401^2+401+1) (degree : ∀ l,Fintype.card {p // I p l}=401+1)
variable (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
variable (neg : negatives C I n 401) (pos : flags C I)

include hn degree unique neg pos in
theorem owner_private (binC : binary C) (line : Bool) (x : Fin n) :
    let r := IncidenceHoistShield.owner line x
    let D := transform C line
    IncidenceStartNormalization.uses D r=1 → ∀ j<D.size, (D.code j).left=r ∨ (D.code j).right=r → (D.code j).op=.meet := by
  let r := IncidenceHoistShield.owner line x
  let sel := select C line
  let D := transform C line
  let v := endpoint C C.size r
  change IncidenceStartNormalization.uses D r=1 → ∀ j<D.size, (D.code j).left=r ∨ (D.code j).right=r → (D.code j).op=.meet
  intro one
  have rawBound : r<n+n := by cases line <;> simp [r,IncidenceHoistShield.owner] <;> omega
  obtain ⟨H,pre,stop⟩ := complete C C.size r {r} (initial C r _ (owner_hot C line x)) (by omega)
  have sourcePos := IncidenceHoistSensitive.exit_used C I hn degree unique neg pos line x pre
  have eq := ref_walk C sel C.size r (IncidenceHoistDisjoint.chooses C I degree unique pos neg hn line x)
  have input : (buildPrefix (n+n) C.code sel C.size).ref r=r := by
    simpa [buildPrefix] using ref_stable (n+n) C.code sel 0 C.size r (by omega)
  have vr : (buildPrefix (n+n) C.code sel C.size).ref v=r := eq.trans input
  have preserve (w : Op → ℕ) : count w v (circuitCode C) ≤ count w r (circuitCode D) := by
    rw [show circuitCode D = codeList (n+n) C.size C.output C.code sel from circuit_code C sel]
    apply exit_count_le
    · intro t ht hit
      have ⟨l,h⟩ := C.earlier t ht
      have before : v<n+n+t := hit.elim (fun e => e ▸ l) (fun e => e ▸ h)
      have stable := ref_stable (n+n) C.code sel t (C.size-t) v before
      rw [show t+(C.size-t)=C.size by omega] at stable
      exact stable.symm.trans vr
    · intro t _ b h
      exact ⟨(selected_safe C neg h).choose_spec.1,not_principal C h stop⟩
  have oldOne : IncidenceStartNormalization.uses C v=1 := by
    have bound := preserve (fun _ => 1)
    rw [actual_uses,actual_uses] at bound
    change IncidenceStartNormalization.uses D r=1 at one
    change 0<IncidenceStartNormalization.uses C v at sourcePos
    omega
  obtain ⟨k,b,read,hk,atPort,_⟩ := unique_reader C v oldOne
  have gate : (C.code k).op=.meet := by
    rcases binC k hk with joined|met
    · have can : step? C v=some (k,b) := by simp [step?,read,oldOne,joined]
      change step? C v=none at stop
      rw [stop] at can
      contradiction
    · exact met
  exact private_meet D r one ((meet_hit C v k b hk atPort gate).trans_le (preserve meetWeight))

#print axioms owner_private
end IncidenceHoistNormalize
