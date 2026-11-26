import ThresholdStarBypass
import ThresholdSharedPairMinimum
import Batteries.Tactic.OpenPrivate
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition ThresholdSharedFlow
open private retained from ThresholdOrPhysicalBook
open private distinct_parts from ThresholdSharedPairMinimum

private theorem probe_gate {C : Circuit} {n : Nat} (L : Layout C n) (u : Id C)
    {w x y : Nat} {op : Op} (g : GateAt C n w op x y) (notU : w≠n+u.val) :
    on L u w=act op (on L u x) (on L u y) := by
  obtain ⟨pre,post,hg,idx⟩ := g.layout
  let i : Id C := ⟨pre.length,by simp [hg]⟩
  have idx' : n+i.val=w := idx.symm
  have ip : L.op i=op ∧ L.left i=x ∧ L.right i=y := by
    have atI := L.atIndex i
    rw [idx'] at atI
    have eq := (gate_lookup atI).symm.trans (gate_lookup g)
    have input := congrArg (fun z : Option Gate => z.map Gate.inputs) eq
    have tag := congrArg (fun z : Option Gate => z.map Gate.op) eq
    cases h : L.op i <;> cases o : op <;> simp_all [binary,gateOp]
  have sep : i≠u := fun e => notU (idx'.symm.trans (by rw [e]))
  have rr := row_eq L u i
  rw [if_neg sep,ip.1,ip.2.1,ip.2.2] at rr
  change on L u (n+i.val)=_ at rr
  rw [idx'] at rr
  cases op <;> exact rr

private theorem probe_tree {C : Circuit} {n : Nat} (L : Layout C n) (u : Id C)
    (t : Tree) (chk : t.Checked C n) (away : n+u.val∉t.gates) :
    on L u t.out=t.exts.any (on L u) := by
  induction t with
  | raw w => change w<n at chk; change on L u w=false; rw [on]; simp [chk]
  | external w => simp [Tree.out,Tree.exts]
  | join w l r hl hr =>
    have neq : w≠n+u.val := by intro e; apply away; simp [Tree.gates,e]
    have a := hl chk.2.1 (fun hit => away (by simp [Tree.gates,hit]))
    have b := hr chk.2.2 (fun hit => away (by simp [Tree.gates,hit]))
    change on L u w=_
    rw [probe_gate L u chk.1 neq]
    simp [act,Tree.exts,a,b]

/-- Compare forced-U physical evaluation and the extracted block scan at every
stored root, including a partner wire. The supplied center membership is a
physical join in its own forest block. -/
theorem probe_book {C : Circuit} {n : Nat} (L : Layout C n) (u : Id C)
    (A : Block) (center : A∈forest L Fin.val) (uOut : A.out=n+u.val)
    (uGate : n+u.val∈A.orIDs) (sel : Nat → Bool) (bs : List Block) (seen : List Nat)
    (inForest : ∀ b∈bs,b∈forest L Fin.val) (bk : Book C n seen bs) (f : Env)
    (same : ∀ w∈seen,f w=on L u w) :
    ∀ w∈outputs bs seen,run (n+u.val) sel false (fun _ => false) bs f w=on L u w := by
  induction bs generalizing seen f with
  | nil => exact same
  | cons b bs ih =>
    obtain ⟨chk,refs,tail⟩ := bk
    have value : row (n+u.val) sel false (fun _ => false) f b=on L u b.out := by
      by_cases over : b.out=n+u.val
      · have hot := row_eq L u u
        change on L u (n+u.val)=_ at hot
        simpa only [row,over,ite_true] using (show on L u (n+u.val)=true by simpa using hot).symm
      cases b with
      | meet w x y =>
        change w≠n+u.val at over
        have hx := same x (refs x (by simp [Block.exts]))
        have hy := same y (refs y (by simp [Block.exts]))
        simpa [row,Block.out,over,act,hx,hy] using (probe_gate L u chk over).symm
      | group p t =>
        change t.out≠n+u.val at over
        have neq : A≠Block.group p t := by intro eq; subst A; exact over uOut
        have dis : n+u.val∉t.gates := by
          intro hit
          have count := distinct_parts _ _ _ neq center (inForest _ (by simp)) _ uGate hit
          have mem : n+u.val∈allGates (forest L Fin.val) := List.mem_flatMap.mpr ⟨A,center,uGate⟩
          have once := List.nodup_iff_count_eq_one.mp (forest_nodup L Fin.val) _ mem
          omega
        have leaves : t.exts.any f=t.exts.any (on L u) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          constructor <;> rintro ⟨j,hj,on'⟩ <;> refine ⟨j,hj,?_⟩
          · rwa [←same j (refs j hj)]
          · rwa [same j (refs j hj)]
        have noRaw : t.raws.any (fun _ => false)=false := by simp [List.any_eq_false]
        simpa [row,Block.out,over,leaves,noRaw] using (probe_tree L u t chk dis).symm
    apply ih _ (fun a ha => inForest a (by simp [ha])) tail _
    intro j hj
    by_cases matchOut : j=b.out
    · subst j; simpa [put] using value
    · simpa [put,matchOut] using same j ((List.mem_cons.mp hj).resolve_left matchOut)

theorem external_stored {C : Circuit} {n} (bs : List Block) (seen : List Nat)
    (bk : Book C n seen bs) (b : Block) (hb : b∈bs) (w : Nat) (hw : w∈b.exts) :
    w∈outputs bs seen := by
  induction bs generalizing seen with
  | nil => simp at hb
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with eq|mem
    · subst a
      exact (retained _ _ _).mpr (Or.inl (by simp [bk.2.1 w hw]))
    · exact ih _ bk.2.2 mem

theorem root_stored (bs : List Block) (b : Block) (hb : b∈bs) :
    b.out∈outputs bs [] := (retained _ _ _).mpr (Or.inr ⟨b,hb,rfl⟩)

theorem hub_center {C : Circuit} {n} (L : Layout C n) (u : Id C)
    (stop : T2OrPartition.next C n u=none) (op : L.op u=.or) :
    ∃ A∈forest L Fin.val,A.out=n+u.val ∧ n+u.val∈A.orIDs := by
  refine ⟨makeBlock L Fin.val u,mem_roots L Fin.val u stop,makeBlock_out L Fin.val u,?_⟩
  unfold makeBlock
  split
  · simp_all
  · simp [Block.orIDs,root,Tree.gates]

#print axioms probe_book
end ThresholdStarBypass
