import ThresholdSlotEvaluation
namespace ThresholdSlotEvaluation
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition
variable {C : Circuit} {n : Nat} {L : Layout C n}
variable {s : Id C → Bool → Bool} {V : Nat → Bool}

def treeValue (raw V : Nat → Bool) : Tree → Bool
  | .raw x => raw x
  | .external x => V x
  | .join w _ _ => V w

theorem tree_eq (T : Trace L s V) (raw : Nat → Bool) (t : Tree)
    (chk : t.Checked C n) (ext : ∀ w∈t.exts,n≤w)
    (slots : ∀ i : Id C, n+i.val∈t.gates →
      (L.left i<n → s i false=raw (L.left i)) ∧
      (L.right i<n → s i true=raw (L.right i))) :
    treeValue raw V t= (t.raws.any raw || t.exts.any V) := by
  induction t with
  | raw x => simp [treeValue,Tree.raws,Tree.exts]
  | external x => simp [treeValue,Tree.raws,Tree.exts]
  | join w l r il ir =>
    obtain ⟨pre,post,hg,idx⟩ := chk.1.layout
    let i : Id C := ⟨pre.length,by simp [hg]⟩
    have hw : n+i.val=w := idx.symm
    have ip : L.op i=.or ∧ L.left i=l.out ∧ L.right i=r.out := by
      have atI := L.atIndex i
      rw [hw] at atI
      have eq := (gate_lookup atI).symm.trans (gate_lookup chk.1)
      have input := congrArg (fun z : Option Gate => z.map Gate.inputs) eq
      have tag := congrArg (fun z : Option Gate => z.map Gate.op) eq
      cases h : L.op i <;> simp_all [binary,gateOp]
    have localSlots := slots i (by simp [Tree.gates,hw])
    have portEq (b : Bool) (z : Tree) (cz : z.Checked C n) (ez : ∀ v∈z.exts,n≤v)
        (sr : z.out<n → s i b=raw z.out) :
        read (n:=n) s V i b z.out=treeValue raw V z := by
      cases z with
      | raw x =>
        change x<n at cz
        simpa [read,Tree.out,treeValue,cz] using sr cz
      | external x =>
        have h := ez x (by simp [Tree.exts])
        simp [read,Tree.out,treeValue,Nat.not_lt.mpr h]
      | join x a b =>
        obtain ⟨pre',post',hg',idx'⟩ := cz.1.layout
        have h : n≤x := by omega
        simp [read,Tree.out,treeValue,Nat.not_lt.mpr h]
    have el : ∀ x∈l.exts,n≤x := fun x hx => ext x (List.mem_append_left _ hx)
    have er : ∀ x∈r.exts,n≤x := fun x hx => ext x (List.mem_append_right _ hx)
    have al := il chk.2.1 el (fun j hj => slots j (by simp [Tree.gates,hj]))
    have ar := ir chk.2.2 er (fun j hj => slots j (by simp [Tree.gates,hj]))
    have vl := portEq false l chk.2.1 el (by simpa [ip.2.1] using localSlots.1)
    have vr := portEq true r chk.2.2 er (by simpa [ip.2.2] using localSlots.2)
    have rr := T.row i
    rw [hw,ip.1,ip.2.1,ip.2.2,vl,vr,al,ar] at rr
    simpa [treeValue,Tree.raws,Tree.exts,act,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm] using rr
end ThresholdSlotEvaluation
