import T2SoleOrEval
namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus

theorem ok_append (a b : List Gate) (k : Nat) :
    SuffixOK k (a++b) ↔ SuffixOK k a ∧ SuffixOK (k+a.length) b := by
  induction a generalizing k with
  | nil => simp [SuffixOK]
  | cons g a ih =>
    simp only [List.cons_append,SuffixOK,ih,List.length_cons]
    rw [show k+1+a.length=k+(a.length+1) by omega]
    tauto

theorem ok_indices (gs : List Gate) (k : Nat) :
    SuffixOK k gs ↔ ∀ j : Fin gs.length,
    ∃ o : Op, ∃ l r : Nat, gs[j]=binary o l r ∧ l<k+j.val ∧ r<k+j.val := by
  induction gs generalizing k with
  | nil => simp [SuffixOK]
  | cons g gs ih =>
    constructor
    · rintro ⟨head,tail⟩ j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa using head
      · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using (ih (k+1)).mp tail i
    · intro H
      refine ⟨by simpa using H 0,(ih (k+1)).mpr ?_⟩
      intro i
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using H i.succ

private theorem shape (g : Gate) (k : Nat) :
    (∃ o : Op, ∃ l r : Nat, g=binary o l r ∧ l<k ∧ r<k) ↔
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length=2 ∧ ∀ a∈g.inputs,a<k := by
  constructor
  · rintro ⟨o,l,r,rfl,hl,hr⟩
    cases o <;> simp_all [binary,gateOp]
  · obtain ⟨o,ports⟩ := g
    rintro ⟨kind,len,fit⟩
    cases ports with
    | nil => simp at len
    | cons l tail =>
      cases tail with
      | nil => simp at len
      | cons r rest =>
        have er : rest=[] := by simpa using len
        subst rest
        rcases kind with h|h
        · change o = GateOp.and at h
          subst o
          exact ⟨.and,l,r,rfl,fit l (by simp),fit r (by simp)⟩
        · change o = GateOp.or at h
          subst o
          exact ⟨.or,l,r,rfl,fit l (by simp),fit r (by simp)⟩

theorem eligible_iff (n : Nat) (C : Circuit) :
    Eligible n C ↔ Computes n C ∧ C.output<n+C.size ∧ SuffixOK n C.gates := by
  unfold Eligible
  rw [ok_indices]
  simp only [shape,Circuit.size]

private theorem rename_bound {h x j k : Nat} (hx : x<h) (passed : h<k) (lt : j<k) :
    ren h x j < k-1 := by
  unfold ren
  split <;> (first | omega | split <;> omega)

theorem ok_rename (gs : List Gate) (h x k : Nat) (hx : x<h) (passed : h<k)
    (ok : SuffixOK k gs) : SuffixOK (k-1) (gs.map (rewire (ren h x))) := by
  induction gs generalizing k with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨⟨o,l,r,rfl,hl,hr⟩,tail⟩ := ok
    refine ⟨⟨o,ren h x l,ren h x r,rfl,rename_bound hx passed hl,rename_bound hx passed hr⟩,?_⟩
    have sub := ih (k+1) (by omega) tail
    simpa [show k-1+1=k by omega] using sub

theorem moved_eligible (n x p out : Nat) (pre post : List Gate)
    (old : Eligible n ⟨pre ++ binary .or x p :: post,out⟩)
    (hx : x<n) (hp : p<n+pre.length)
    (clean : ∀ s : Finset (Fin n), s.card<2 → (run pre (vector s)).getD p false=false) :
    Eligible n (moved n x p pre post out) := by
  obtain ⟨computes,outRange,valid⟩ := (eligible_iff _ _).mp old
  change out<n+(pre ++ binary .or x p :: post).length at outRange
  have full : out<n+pre.length+1+post.length := by simp at outRange; omega
  obtain ⟨preOK,skip⟩ := (ok_append pre _ n).mp valid
  have tail : SuffixOK (n+pre.length+1) post := skip.2
  apply (eligible_iff _ _).mpr
  refine ⟨moved_computes n x p out pre post computes hx hp full tail clean,?_,?_⟩
  · simp [moved,Circuit.size]
  · let h := n+pre.length
    have shrunk := ok_rename post h x (h+1) (by dsimp [h]; omega) (by omega) tail
    have cutOK : SuffixOK n (short n x pre post out).gates := by
      apply (ok_append pre _ n).mpr
      exact ⟨preOK,by simpa [h] using shrunk⟩
    have e := rename_bound (h:=h) (x:=x) (k:=h+1+post.length) (by dsimp [h]; omega) (by omega) full
    apply (ok_append _ _ n).mpr
    refine ⟨cutOK,⟨⟨.or,_,_,rfl,?_,?_⟩,trivial⟩⟩
    · simp [short,h] at *; omega
    · simp [short]; omega
end T2SoleOrSplice
