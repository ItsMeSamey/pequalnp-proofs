import IncidencePinLosses
namespace IncidenceRunPinPhysical
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceRunPinCompile
open IncidencePinCompensation IncidencePinLowLedger IncidencePinLosses IncidenceZeroRestriction
variable {n : Nat}

def lower (P Q : Finset (Fin n)) (x : Input n) : Input n :=
  (fun p => if p∈P then false else x.1 p, fun l => if l∈Q then false else x.2 l)
def upper (P Q : Finset (Fin n)) (x : Input n) : Input n :=
  (fun p => if p∈P then true else x.1 p, fun l => if l∈Q then false else x.2 l)

theorem residual (C : Circuit n) (bin : binary C) (P Q : Finset (Fin n))
    (on : ∃ x, lower P Q x∈C.wire C.output) (off : ∃ x, upper P Q x∉C.wire C.output) :
    ∃ D : Circuit n, binary D ∧
      D.size+(charged C (z C P Q)).card+(IncidencePhysicalPinExpectation.forced C P).card ≤ C.size ∧
      (lower P Q ⁻¹' C.wire C.output) ⊆ D.wire D.output ∧
      D.wire D.output ⊆ (upper P Q ⁻¹' C.wire C.output) := by
  classical
  let init := fun i => if z C P Q i then Ref.zero else Ref.wire i
  let p := compile (n+n) (n+n) C.code init (z C P Q) (force C P) C.size
  let Y := wires (n+n) C.wire p.gates
  have order (j) (hj : j<C.size) : OrderedBinary (C.code j) (n+n+j) :=
    ⟨(C.earlier j hj).1,(C.earlier j hj).2,bin j hj⟩
  have darkInit (i) (_ : i<n+n) (h : z C P Q i=true) : init i=.zero := by simp [init,h]
  have bounds (i) (hi : i<n+n) : below (n+n) (init i) := by
    cases h : z C P Q i <;> simp [init,h,below,hi]
  obtain ⟨rb,gb⟩ := typed (n+n) (n+n) C.code init (z C P Q) (force C P) bounds C.size order
  change ∀ j (h : j<p.gates.length), OrderedBinary p.gates[j] (n+n+j) at gb
  have model := wires_model (n+n) C.wire p.gates gb
  have dark (i) (hi : i<n+n+C.size) (h : z C P Q i=true) : lower P Q ⁻¹' C.wire i=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply (marks C P Q i).mp h
    apply IncidenceHoistSparse.wire_up C i hi _ hx
    exact ⟨fun k hk => by simpa [freeMax] using (show k∉P by intro mem; simp [lower,mem] at hk),
      fun k hk => by simpa [freeMax] using (show k∉Q by intro mem; simp [lower,mem] at hk)⟩
  have hot (j) (hj : j<C.size) (hf : force C P j=true) : upper P Q ⁻¹' C.wire (n+n+j)=Set.univ := by
    obtain ⟨_,hit,_⟩ := (Finset.mem_filter.mp ((force_iff C P j hj).mp hf)).2
    apply Set.eq_univ_of_forall
    intro x
    apply IncidenceHoistSparse.wire_up C _ (by omega) _ hit
    exact ⟨fun k hk => by simpa [upper, (show k∈P by simpa [IncidenceEligiblePin.pinMask] using hk)],
      fun k hk => by simp [IncidenceEligiblePin.pinMask] at hk⟩
  have inp (i) (hi : i<n+n) : (lower P Q ⁻¹' C.wire i) ⊆ IncidenceRunPinCompile.read Y (init i) ∧
      IncidenceRunPinCompile.read Y (init i) ⊆ (upper P Q ⁻¹' C.wire i) := by
    cases hf : z C P Q i with
    | true => simp [init,hf,IncidenceRunPinCompile.read,dark i (by omega) hf]
    | false =>
      simp only [init,hf,Bool.false_eq_true,ite_false,IncidenceRunPinCompile.read,Y,wires_inputs _ _ _ _ hi]
      have alive : freeMax P Q ∈C.wire i := by
        by_contra h; have := (marks C P Q i).mpr h; simp_all
      by_cases small : i<n
      · let k : Fin n := ⟨i,small⟩
        rw [(C.inputs k).1] at alive ⊢
        have h : k∉P := by simpa [freeMax] using alive
        exact ⟨fun x hx => by simpa [lower,h] using hx,fun x hx => by simpa [upper,h] using hx⟩
      · let k : Fin n := ⟨i-n,by omega⟩
        have eq : i=n+k.val := by dsimp [k]; omega
        rw [eq,(C.inputs k).2] at alive ⊢
        have h : k∉Q := by simpa [freeMax] using alive
        exact ⟨fun x hx => by simpa [lower,h] using hx,fun x hx => by simpa [upper,h] using hx⟩
  have law (f : Input n → Input n) (j) (hj : j<C.size) :
      f ⁻¹' C.wire (n+n+j) = (C.code j).eval (fun i=>f ⁻¹' C.wire i) := by
    rw [C.law j hj,preimage_gate]
  have br := sandwich (n+n) (n+n) C.code init (z C P Q) (force C P)
    (fun i=>lower P Q ⁻¹' C.wire i) (fun i=>upper P Q ⁻¹' C.wire i) Y C.size
    inp order (law _) (law _) dark hot model C.output C.output_lt
  change _ ⊆ IncidenceRunPinCompile.read Y (p.refs C.output) ∧ IncidenceRunPinCompile.read Y (p.refs C.output) ⊆ _ at br
  cases e : p.refs C.output with
  | zero =>
    obtain ⟨x,h⟩ := on
    exact False.elim (by have := br.1 h; simpa [e,IncidenceRunPinCompile.read] using this)
  | one =>
    obtain ⟨x,h⟩ := off
    exact False.elim (h (br.2 (by simp [e,IncidenceRunPinCompile.read])))
  | wire o =>
    let code := fun j => p.gates.getD j ⟨.zero,0,0⟩
    have atCode (j) (h : j<p.gates.length) : code j=p.gates[j] := by
      simp [code,List.getD_eq_getElem?_getD,h]
    let D : Circuit n := {
      size := p.gates.length, output := o, code := code, wire := Y
      output_lt := rb _ C.output_lt _ e
      earlier := fun j h => by rw [atCode j h]; exact ⟨(gb j h).1,(gb j h).2.1⟩
      law := fun j h => by rw [atCode j h]; exact model j h
      inputs := fun k => by
        simp only [Y,wires_inputs _ _ _ _ (show k.val<n+n by omega),
          wires_inputs _ _ _ _ (show n+k.val<n+n by omega)]
        exact C.inputs k }
    refine ⟨D,fun j h => ?_,?_,?_,?_⟩
    · change (code j).op=_ ∨ (code j).op=_
      rw [atCode j h]; exact (gb j h).2.2
    · have budget := room (n+n) (n+n) C.code init (z C P Q) (force C P) darkInit C.size order
      rw [separate_loss] at budget
      simpa [D,p,Nat.add_assoc] using budget
    · simpa [D,e,IncidenceRunPinCompile.read] using br.1
    · simpa [D,e,IncidenceRunPinCompile.read] using br.2

theorem witnesses (C : Circuit n) (I : Fin n → Fin n → Prop) (pos : flags C I)
    (neg : negatives C I n 2) (P Q : Finset (Fin n))
    (flag : ∃ p∉P, ∃ l∉Q, I p l) :
    (∃ x, lower P Q x∈C.wire C.output) ∧ (∃ x, upper P Q x∉C.wire C.output) := by
  obtain ⟨p,hp,l,hl,inc⟩ := flag
  constructor
  · refine ⟨(single p,single l),?_⟩
    have e : lower P Q (single p,single l)=(single p,single l) := by
      apply Prod.ext <;> funext i
      · by_cases mem : i∈P
        · have ne : i≠p := fun e => hp (e ▸ mem)
          simp [lower,mem,single,ne]
        · simp [lower,mem]
      · by_cases mem : i∈Q
        · have ne : i≠l := fun e => hl (e ▸ mem)
          simp [lower,mem,single,ne]
        · simp [lower,mem]
    rw [e]
    exact pos p l inc
  · let empty : Input n := (fun _ => false,fun _ => false)
    refine ⟨empty,?_⟩
    apply neg
    · simpa [upper,empty] using (show P.card ≤ n by simpa using Finset.card_le_univ P)
    · simp [upper,empty]
    · intro p l hp hl; simp [upper,empty] at hl

#print axioms witnesses
#print axioms residual
end IncidenceRunPinPhysical
