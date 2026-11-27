import IncidencePinHoistSparse
import IncidenceHoistNormalize
import IncidenceHoistLive
namespace IncidenceTwoLineNormalize
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistFlow IncidenceHoistWalk
open IncidenceHoistEndpoint IncidenceHoistReaders IncidenceHoistPorts IncidenceHoistCompile
open IncidenceHoistPrefix IncidenceHoistStage HoistPhysicalPorts IncidenceHoistRealize
open IncidenceHoistPrune
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
variable (degree : ∀ l, Fintype.card {p // I p l} = 401+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
variable (pos : flags C I) (neg : negatives C I n 2)

private theorem singleBound (x : Fin n) : Fintype.card {j // single x j=true} ≤ 1 := by
  let f : {j // single x j=true} → Unit := fun _ => ()
  have h : Function.Injective f := by
    intro a b _
    exact Subtype.ext ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
  simpa using Fintype.card_le_of_injective f h

include degree unique pos neg in
theorem no_opposite (j : ℕ) (b d : Bool)
    (a : (j,b)∈pool C true) (c : (j,d)∈pool C true) : b=d := by
  obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp a
  obtain ⟨y,_,hy⟩ := List.mem_flatMap.mp c
  obtain ⟨_,valid,sh⟩ := walk_shields C (IncidencePinHoistSparse.witness_neg C I neg true x) _ _ _
    (initial C _ _ (owner_hot C true x)) (j,b) hx
  have hit := walk_hot C _ _ _ (initial C _ _ (owner_hot C true y)) (j,d) hy
  have ⟨hl,hr⟩ := C.earlier j valid
  have bound : other (C.code j) b<n+n+C.size := by
    cases b <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
  have no : witness true y ∉ C.wire (other (C.code j) b) :=
    IncidencePinHoistSparse.line_safe C I degree unique pos neg x _ bound sh
      (fun _ => false) (single y) ((singleBound y).trans (by decide)) (by simp)
  by_contra diff
  have eq : keep (C.code j) d = other (C.code j) b := by cases b <;> cases d <;> simp_all [keep,other]
  exact no (eq ▸ hit)

private theorem find_gate (xs : List (ℕ × Bool)) (j : ℕ) (b : Bool)
    (inside : (j,b)∈xs) (only : ∀ d, (j,d)∈xs → d=b) :
    xs.find? (fun e => decide (e.1=j))=some (j,b) := by
  induction xs with
  | nil => simp at inside
  | cons p xs ih =>
    obtain ⟨k,d⟩ := p
    by_cases same : k=j
    · subst k
      have db := only d (by simp)
      simp [List.find?,db]
    · have tail : (j,b)∈xs := (List.mem_cons.mp inside).resolve_left (by intro h; exact same (congrArg Prod.fst h).symm)
      have back := ih tail (fun v hv => only v (List.mem_cons_of_mem _ hv))
      simpa [List.find?,same] using back

include degree unique pos neg in
theorem chooses (x : Fin n) (e : ℕ × Bool)
    (inWalk : e∈walk C C.size (IncidenceHoistShield.owner true x)) :
    select C true e.1=some e.2 := by
  obtain ⟨j,b⟩ := e
  have inPool : (j,b)∈pool C true := List.mem_flatMap.mpr ⟨x,by simp,inWalk⟩
  have pick := find_gate (pool C true) j b inPool (fun d hd =>
    no_opposite C I degree unique pos neg j d b hd inPool)
  simp [select,pick]

include degree unique neg pos in
theorem owner_private (binC : binary C) (x : Fin n) :
    let r := IncidenceHoistShield.owner true x
    let D := transform C true
    IncidenceStartNormalization.uses D r=1 → ∀ j<D.size, (D.code j).left=r ∨ (D.code j).right=r → (D.code j).op=.meet := by
  let r := IncidenceHoistShield.owner true x
  let sel := select C true
  let D := transform C true
  let v := endpoint C C.size r
  change IncidenceStartNormalization.uses D r=1 → ∀ j<D.size, (D.code j).left=r ∨ (D.code j).right=r → (D.code j).op=.meet
  intro one
  have rawBound : r<n+n := by simp [r,IncidenceHoistShield.owner]
  obtain ⟨H,pre,stop⟩ := complete C C.size r {r} (initial C r _ (owner_hot C true x)) (by omega)
  have sourcePos := IncidencePinHoistSparse.line_exit_used C I degree pos neg x pre
  have eq := ref_walk C sel C.size r (chooses C I degree unique pos neg x)
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
      exact ⟨(IncidencePinHoistSparse.selected_shield C I neg h).choose_spec.1,not_principal C h stop⟩
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

theorem output_bounds (neg : negatives C I n 2) (line : Bool) :
    C.wire C.output ⊆ (transform C line).wire (transform C line).output ∧
    (transform C line).wire (transform C line).output ⊆ C.wire C.output ∪
      lost C.size C.code (select C line) C.wire := by
  let sel := select C line
  let Y := value C.wire C.code sel (n+n) C.size
  have op (j : ℕ) (_ : j<C.size) (b : Bool) (h : sel j=some b) : (C.code j).op=.join := by
    obtain ⟨_,join,_,_⟩ := IncidencePinHoistSparse.selected_shield C I neg h
    exact join
  have hs := sandwich (n+n) C.size C.wire C.code sel C.earlier C.law op
  have he : (transform C line).wire (transform C line).output=Y C.output ∪ lost C.size C.code sel Y :=
    realize C sel
  rw [he]
  refine ⟨(hs _ C.output_lt).2,?_⟩
  rintro z (old|⟨j,hj,b,hb,hit⟩)
  · exact Or.inl ((hs _ C.output_lt).1 old)
  · have ⟨l,r⟩ := C.earlier j hj
    have bound : other (C.code j) b<n+n+C.size := by
      cases b <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
    exact Or.inr ⟨j,hj,b,hb,(hs _ bound).1 hit⟩


include degree unique pos neg in
theorem normalize (bin : binary C) (src : Live C) :
    let D := transform C true
    D.size=C.size ∧ binary D ∧ flags D I ∧ negatives D I n 2 ∧ soleAnd D n ∧ Live D := by
  let D := transform C true
  have bounds := output_bounds C I neg true
  refine ⟨rfl,ops C true bin,fun p l inc => bounds.1 (pos p l inc),?_,?_,IncidenceHoistLive.live C _ src⟩
  · intro a b ha hb ind present
    rcases bounds.2 present with old|⟨j,_,d,hd,hit⟩
    · exact neg a b ha hb ind old
    · obtain ⟨_,_,_,_,cold⟩ := IncidencePinHoistSparse.selected C I degree unique pos neg hd
      exact cold a b hb ind hit
  · intro i hi
    exact owner_private C I degree unique pos neg bin ⟨i,hi⟩

#print axioms normalize
end IncidenceTwoLineNormalize
