import IncidencePinLowLedger
import IncidencePinHoistSparse
import IncidenceThetaSibling
import IncidencePhysicalPinExpectation
namespace IncidencePinCompensation
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistReaders IncidenceHoistWalk
open IncidenceHoistPrefix IncidenceHoistSparse IncidenceHoistPrune IncidencePinLowLedger
variable {n : Nat} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]

def freeMax (P Q : Finset (Fin n)) : Input n :=
  (fun p => decide (p∉P),fun l => decide (l∉Q))

noncomputable def z (P Q : Finset (Fin n)) (i : Nat) : Bool := by
  classical exact decide (freeMax P Q∉C.wire i)

theorem marks (P Q : Finset (Fin n)) (i : Nat) : z C P Q i=true ↔ freeMax P Q∉C.wire i := by
  classical simp [z]

theorem zero_law (bin : binary C) (P Q : Finset (Fin n)) (j : Nat) (hj : j<C.size) :
    z C P Q (n+n+j)=IncidenceOperandLedger.zeroAt (z C P Q) (C.code j) := by
  classical
  rcases bin j hj with op|op <;>
    simp [z,IncidenceOperandLedger.zeroAt,op,C.law j hj,Gate.eval,Op.eval,not_and_or]

def pinRaw (P : Finset (Fin n)) := P.image Fin.val
def lineRaw (Q : Finset (Fin n)) := Q.image (fun l=>n+l.val)

theorem raw_set (P Q : Finset (Fin n)) : deadRaw C (z C P Q) =pinRaw P ∪ lineRaw Q := by
  classical
  ext i
  simp only [deadRaw,Finset.mem_filter,Finset.mem_range,marks,Finset.mem_union,pinRaw,lineRaw,
    Finset.mem_image]
  by_cases small : i<n
  · let p : Fin n := ⟨i,small⟩
    rw [(C.inputs p).1]
    change (i<n+n ∧ ¬ decide (p∉P)=true) ↔ _
    simp only [decide_eq_true_eq,not_not]
    constructor
    · exact fun h => Or.inl ⟨p,h.2,rfl⟩
    · rintro (⟨a,ha,e⟩|⟨a,_,e⟩)
      · have pe : a=p := Fin.ext e
        exact ⟨by omega,pe ▸ ha⟩
      · omega
  · by_cases inside : i<n+n
    · let l : Fin n := ⟨i-n,by omega⟩
      have eq : n+l.val=i := by dsimp [l]; omega
      rw [← eq,(C.inputs l).2]
      change (n+l.val<n+n ∧ ¬ decide (l∉Q)=true) ↔ _
      simp only [decide_eq_true_eq,not_not]
      constructor
      · exact fun h => Or.inr ⟨l,h.2,rfl⟩
      · rintro (⟨a,_,e⟩|⟨a,ha,e⟩)
        · have := a.isLt; omega
        · have pe : a=l := Fin.ext (by omega)
          exact ⟨by omega,pe ▸ ha⟩
    · constructor
      · omega
      · rintro (⟨a,_,e⟩|⟨a,_,e⟩) <;> have := a.isLt <;> omega

theorem raw_card (P Q : Finset (Fin n)) : (deadRaw C (z C P Q)).card=P.card+Q.card := by
  rw [raw_set,Finset.card_union_of_disjoint]
  · unfold pinRaw lineRaw
    rw [Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (by intro a b e; exact Fin.ext (Nat.add_left_cancel e))]
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p,_,ep⟩ := Finset.mem_image.mp hi
    obtain ⟨l,_,el⟩ := Finset.mem_image.mp hj
    have := p.isLt
    omega

theorem all_used (neg : negatives C I n 2) (pos : flags C I)
    (hasPoint : ∀ l,∃ p,I p l) (hasLine : ∀ p,∃ l,I p l) (i : Nat) (hi : i<n+n) :
    0<IncidenceStartNormalization.uses C i := by
  by_cases left : i<n
  · let x : Fin n := ⟨i,left⟩
    obtain ⟨y,inc⟩ := hasLine x
    exact IncidencePinHoistSparse.exit_used_of_neighbor C I neg pos false x y inc
      (initial C i _ (owner_hot C false x))
  · let x : Fin n := ⟨i-n,by omega⟩
    obtain ⟨y,inc⟩ := hasPoint x
    have eq : n+x.val=i := by dsimp [x]; omega
    rw [←eq]
    exact IncidencePinHoistSparse.exit_used_of_neighbor C I neg pos true x y inc
      (initial C _ _ (owner_hot C true x))

theorem credit_line (bin : binary C) (andL : soleAnd C n)
    (neg : negatives C I n 2) (pos : flags C I) (P Q : Finset (Fin n)) (x p : Fin n)
    (dead : x∈Q) (free : p∉P) (inc : I p x) (one : IncidenceStartNormalization.uses C (n+x.val)=1) :
    ∃ j<C.size,(C.code j).op=.meet ∧ z C P Q (C.code j).left≠z C P Q (C.code j).right ∧
        (if z C P Q (C.code j).left then (C.code j).left else (C.code j).right)=n+x.val := by
  classical
  obtain ⟨j,d,_,hj,hp,only⟩ := unique_reader C _ one
  have op := andL x.val x.isLt one j hj (by cases d; exact Or.inr hp; exact Or.inl hp)
  have otherNe : operand (C.code j) (!d)≠n+x.val := by
    intro h
    have bad := (only j hj (!d) h).2
    cases d <;> contradiction
  have outNe : C.output≠n+x.val := fun e =>
    IncidencePinHoistSparse.witness_neg C I neg true x (e.symm ▸ owner_hot C true x)
  let a : Input n := (single p,single x)
  let b := witness false p
  have same (i : Nat) (hi : i<n+n) (different : i≠n+x.val) : a∈C.wire i ↔ b∈C.wire i := by
    by_cases small : i<n
    · rw [(C.inputs ⟨i,small⟩).1]; rfl
    · let l : Fin n := ⟨i-n,by omega⟩
      have eq : n+l.val=i := by dsimp [l]; omega
      have ne : l≠x := by intro e; apply different; rw [← eq,e]
      rw [← eq,(C.inputs l).2]
      simp [a,b,witness,single,ne]
  have active := IncidenceThetaSibling.physical (n+n) C.size (n+x.val) j C.output C.code C.wire
    (fun k hk => ⟨(C.earlier k hk).1,(C.earlier k hk).2,bin k hk⟩) C.law hj op (!d)
    (fun k hk ne => ⟨fun e => ne (only k hk true e).1,fun e => ne (only k hk false e).1⟩)
    otherNe C.output_lt outNe a b same (pos p x inc) (IncidencePinHoistSparse.witness_neg C I neg false p)
  have sideBound : operand (C.code j) (!d)<n+n+C.size := by
    have ⟨l,r⟩ := C.earlier j hj
    cases d <;> simp [operand] <;> omega
  have up : freeMax P Q∈C.wire (operand (C.code j) (!d)) := by
    apply wire_up C _ sideBound _ active
    refine ⟨?_,?_⟩
    · intro k h
      have eq : k=p := of_decide_eq_true h
      subst k
      exact decide_eq_true free
    · simp [b,witness]
  have low : z C P Q (n+x.val)=true := by
    apply (marks C P Q _).mpr
    rw [(C.inputs x).2]
    simpa [freeMax] using dead
  have high : z C P Q (operand (C.code j) (!d))=false := by simp [z,up]
  refine ⟨j,hj,op,?_⟩
  cases d <;> simp only [operand,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false] at hp high <;>
    simp [hp,high,low]

theorem free_pair (pos : flags C I) (P Q : Finset (Fin n))
    (p l : Fin n) (fp : p∉P) (fl : l∉Q) (inc : I p l) : z C P Q C.output=false := by
  classical
  have hit : freeMax P Q∈C.wire C.output := by
    apply wire_up C _ C.output_lt _ (pos p l inc)
    refine ⟨?_,?_⟩
    · intro i h
      have e : i=p := of_decide_eq_true h
      subst i
      exact decide_eq_true fp
    · intro i h
      have e : i=l := of_decide_eq_true h
      subst i
      exact decide_eq_true fl
  simp [z,hit]

theorem raw_budget (bin : binary C) (live : Live C) (andL : soleAnd C n)
    (neg : negatives C I n 2) (pos : flags C I) (P Q : Finset (Fin n))
    (hasPoint : ∀ l,∃ p,I p l) (hasLine : ∀ p,∃ l,I p l)
    (available : ∀ x∈Q, ∃ p∉P,I p x) (survives : ∃p∉P,∃l∉Q,I p l) :
    2*(P.card+Q.card) ≤ (charged C (z C P Q)).card+P.card := by
  classical
  obtain ⟨p,fp,l,fl,inc⟩ := survives
  have b := budget C (z C P Q) (pinRaw P) bin live (free_pair C I pos P Q p l fp fl inc)
    (zero_law C bin P Q) (fun i hi => all_used C I neg pos hasPoint hasLine i
      (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)) (by
      intro i all nonPin one
      rw [raw_set] at all
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ((Finset.mem_union.mp all).resolve_left nonPin)
      obtain ⟨a,free,flag⟩ := available x hx
      subst i
      exact credit_line C I bin andL neg pos P Q x a hx free flag one)
  simpa [raw_card,pinRaw,Finset.card_image_of_injective _ Fin.val_injective] using b

theorem forced_separate (P Q : Finset (Fin n)) (g : Fin C.size)
    (forced : g∈IncidencePhysicalPinExpectation.forced C P) :
    g.val∉charged C (z C P Q) := by
  classical
  obtain ⟨_,_,⟨p,fp,a⟩,⟨l,fl,b⟩⟩ := (Finset.mem_filter.mp forced).2
  have high (w : Nat) (bound : w<n+n+C.size) (x : Fin n) (surv : x∉P)
      (h : IncidenceLineRoutedSlots.hit C w x) : z C P Q w=false := by
    have m : freeMax P Q∈C.wire w := by
      apply wire_up C w bound _ h
      refine ⟨?_,by simp⟩
      intro j hj
      have e : j=x := of_decide_eq_true hj
      subst j
      exact decide_eq_true surv
    simp [z,m]
  have ⟨hl,hr⟩ := C.earlier g.val g.isLt
  have lz := high _ (by have := g.isLt; omega) p fp a
  have rz := high _ (by have := g.isLt; omega) l fl b
  simp [charged,lz,rz]

#print axioms raw_budget
#print axioms forced_separate
end IncidencePinCompensation
