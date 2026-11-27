import IncidenceHoistPrune
import IncidenceHoistCompile
namespace IncidenceHoistLive
open CircuitRewire IncidenceStartNormalization IncidenceHoistCompile IncidenceHoistFlow IncidenceHoistPrune

def Back (m : ℕ) (L : ℕ→Prop) (gs : List Gate) :=
  ∀ i (hi : i<gs.length), L (m+i) → L gs[i].left ∧ L gs[i].right

private theorem parts (m : ℕ) (L : ℕ→Prop) (gs hs : List Gate) (h : Back m L (gs++hs)) :
    Back m L gs ∧ Back (m+gs.length) L hs := by
  constructor
  · intro i hi
    have x := h i (by simp; omega)
    rwa [List.getElem_append_left hi] at x
  · intro i hi
    have x := h (gs.length+i) (by simpa using hi)
    simpa [List.getElem_append_right (show gs.length≤gs.length+i by omega),Nat.add_assoc] using x

private def finish (n a : ℕ) (xs : List ℕ) := if xs.isEmpty then a else n+xs.length-1

private theorem joins (n a : ℕ) (xs : List ℕ) (L : ℕ→Prop)
    (h : Back n L (appendJoins n a xs)) (hl : L (finish n a xs)) :
    L a ∧ (∀ x∈xs,L x) ∧ ∀ i<xs.length,L (n+i) := by
  induction xs generalizing n a with
  | nil => exact ⟨hl,by simp,by simp⟩
  | cons x xs ih =>
    let g : Gate := ⟨.join,a,x⟩
    have split := parts n L [g] (appendJoins (n+1) n xs) h
    have f : finish n a (x::xs)=finish (n+1) n xs := by
      cases xs <;> simp [finish] <;> omega
    obtain ⟨head,tail,indices⟩ := ih (n+1) n split.2 (f ▸ hl)
    have first := split.1 0 (by simp) (by simpa using head)
    refine ⟨first.1,?_,?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|inside
      · exact first.2
      · exact tail i inside
    · intro i hi
      cases i with
      | zero => simpa using head
      | succ i =>
        have hh : i<xs.length := by simpa using hi
        simpa [Nat.add_assoc,Nat.add_comm 1 i] using indices i hh

private theorem prefix_back (m : ℕ) (code : ℕ→Gate) (sel : ℕ→Option Bool) (L : ℕ→Prop) (t : ℕ)
    (ordered : ∀ j<t, (code j).left<m+j ∧ (code j).right<m+j)
    (back : Back m L (buildPrefix m code sel t).kept)
    (sibs : ∀ i∈(buildPrefix m code sel t).siblings,L i) :
    let p := buildPrefix m code sel t
    (∀ j<t, L (p.ref (m+j)) → L (p.ref (code j).left) ∧ L (p.ref (code j).right)) ∧
    ∀ i<p.kept.length,∃ j<t,p.ref (m+j)=m+i := by
  induction t with
  | zero => simp [buildPrefix]
  | succ t ih =>
    let p := buildPrefix m code sel t
    have old (j : ℕ) (hj : j<t) := ordered j (by omega)
    have ⟨hl,hr⟩ := ordered t (by omega)
    cases e : sel t with
    | none =>
      have ba := parts m L p.kept [redirect p.ref (code t)] (by simpa [buildPrefix,e,p] using back)
      obtain ⟨prior,origin⟩ := ih old ba.1 (by simpa [buildPrefix,e] using sibs)
      constructor
      · intro j hj hit
        by_cases eq : j=t
        · subst j
          have last := ba.2 0 (by simp) (by simpa [buildPrefix,e,put,p] using hit)
          simpa [buildPrefix,e,put,show (code t).left ≠ m+t by omega,
            show (code t).right ≠ m+t by omega,p,redirect] using last
        · have before : j<t := by omega
          have ⟨l,r⟩ := old j before
          simp [buildPrefix,e,put,show j≠t by omega,show (code j).left≠m+t by omega,
            show (code j).right≠m+t by omega] at hit ⊢
          exact prior j before hit
      · intro i hi
        by_cases early : i<p.kept.length
        · obtain ⟨j,hj,eq⟩ := origin i early
          exact ⟨j,by omega,by simpa [buildPrefix,e,put,show j≠t by omega] using eq⟩
        · have endIx : i=p.kept.length := by simp [buildPrefix,e,p] at hi; dsimp [p] at early ⊢; omega
          exact ⟨t,by omega,by simp [buildPrefix,e,put,endIx,p]⟩
    | some b =>
      have ba : Back m L p.kept := by simpa [buildPrefix,e,p] using back
      have oldS (i : ℕ) (h : i∈p.siblings) : L i :=
        sibs i (by simp [buildPrefix,e,p] at h ⊢; exact Or.inl h)
      have side : L (p.ref (other (code t) b)) :=
        sibs _ (by simp [buildPrefix,e,p])
      obtain ⟨prior,origin⟩ := ih old ba oldS
      constructor
      · intro j hj hit
        by_cases eq : j=t
        · subst j
          have main : L (p.ref (keep (code t) b)) := by simpa [buildPrefix,e,put,p] using hit
          simp only [buildPrefix,e,put,if_neg (show (code t).left≠m+t by omega),
            if_neg (show (code t).right≠m+t by omega)]
          cases b <;> simp only [keep,other,Bool.false_eq_true,if_true,if_false] at main side <;> tauto
        · have before : j<t := by omega
          have ⟨l,r⟩ := old j before
          simp [buildPrefix,e,put,show j≠t by omega,show (code j).left≠m+t by omega,
            show (code j).right≠m+t by omega] at hit ⊢
          exact prior j before hit
      · intro i hi
        obtain ⟨j,hj,eq⟩ := origin i (by simpa [buildPrefix,e] using hi)
        exact ⟨j,by omega,by simpa [buildPrefix,e,put,show j≠t by omega] using eq⟩


/-- Physical liveness is preserved even with sharing and same-shore crossings. -/
theorem live {n : ℕ} (C : Circuit n) (sel : ℕ→Option Bool) (src : Live C) :
    Live (circuit C sel) := by
  let m := n+n
  let D := circuit C sel
  let p := buildPrefix m C.code sel C.size
  let gs := codeList m C.size C.output C.code sel
  let L := Anc D
  have len : gs.length=C.size := physical_size ..
  have back : Back m L gs := by
    intro i hi parent
    have bound : i<D.size := len ▸ hi
    have eh : D.code i=gs[i] := by change gs.getD i _=_; simp [List.getD_eq_getElem?_getD,hi]
    exact ⟨eh ▸ Anc.left i bound parent,eh ▸ Anc.right i bound parent⟩
  have ⟨kept,app⟩ := parts m L p.kept (appendJoins (m+p.kept.length) (p.ref C.output) p.siblings) back
  have endpoint : finish (m+p.kept.length) (p.ref C.output) p.siblings=D.output := by
    change _=finalOutput m C.size C.output C.code sel
    have balance := prefix_length m C.code sel C.size
    change p.kept.length+p.siblings.length=C.size at balance
    simp only [finish,finalOutput]
    change (if p.siblings.isEmpty then _ else _)=(if p.siblings.isEmpty then _ else _)
    split <;> first | rfl | omega
  have ⟨out,side,appLive⟩ := joins _ _ _ _ app (endpoint.symm ▸ Anc.output)
  have ⟨parents,origin⟩ := prefix_back m C.code sel L C.size C.earlier kept side
  have maps (j : ℕ) (h : Anc C j) : L (p.ref j) := by
    induction h with
    | output => exact out
    | left j h _ ih => exact (parents j h ih).1
    | right j h _ ih => exact (parents j h ih).2
  intro k hk
  change L (m+k)
  by_cases old : k<p.kept.length
  · obtain ⟨j,v,eq⟩ := origin k old
    exact eq ▸ maps _ (src j v)
  · have balance := prefix_length m C.code sel C.size
    change p.kept.length+p.siblings.length=C.size at balance
    change k<C.size at hk
    have h := appLive (k-p.kept.length) (by omega)
    rwa [show m+p.kept.length+(k-p.kept.length)=m+k by omega] at h

#print axioms live
end IncidenceHoistLive
