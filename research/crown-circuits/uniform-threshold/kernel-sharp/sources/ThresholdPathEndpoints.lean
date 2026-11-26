import ThresholdFirstActive
import ThresholdSimpleIncidence
import ThresholdSharedOrBudget

namespace ThresholdFirstActive
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice ThresholdQuarterCubes ThresholdSimpleIncidence ThresholdRegularSource
variable {C : Circuit} {n : Nat} {L : Layout C n} {x : Fin n}

private theorem invert_path {w l r : Nat} (g : GateAt C n w .or l r)
    (p : OrPath L x w) : OrPath L x l ∨ OrPath L x r := by
  cases p with
  | raw =>
    obtain ⟨⟨pre,post,_,num⟩,_,_⟩ := g
    have := x.isLt
    omega
  | left op path =>
    have eq := or_operands_unique g (op ▸ L.atIndex _)
    exact Or.inl (eq.1.symm ▸ path)
  | right op path =>
    have eq := or_operands_unique g (op ▸ L.atIndex _)
    exact Or.inr (eq.2.symm ▸ path)

private theorem raw_origin {w : Nat} (lt : w<n) (p : OrPath L x w) : w=x.val := by
  cases p with
  | raw => rfl
  | left => omega
  | right => omega

def ReadsOR (L : Layout C n) (w : Nat) : Prop :=
  ∃ i : T2OrPartition.Id C, L.op i = .or ∧ (L.left i=w ∨ L.right i=w)

private theorem join_reader {w l r : Nat} (g : GateAt C n w .or l r) :
    ReadsOR L l ∧ ReadsOR L r := by
  obtain ⟨⟨pre,post,eq,num⟩,gl,gr⟩ := g
  let i : T2OrPartition.Id C := ⟨pre.length,by simp [eq]⟩
  have wi : w=n+i.val := num
  have same := gate_lookup (L.atIndex i)
  have os : L.op i = .or := by
    have lookup : C.gates.get i = binary .or l r := by simp [i,eq,List.get_eq_getElem]
    have src : C.gates.get i = binary (L.op i) (L.left i) (L.right i) := by simpa using same
    have tag := congrArg Gate.op (src.symm.trans lookup)
    cases z : L.op i <;> simp_all [binary,gateOp]
  have g' : GateAt C n (n+i.val) .or l r := by
    exact ⟨⟨pre,post,eq,rfl⟩,wi ▸ gl,wi ▸ gr⟩
  obtain ⟨hl,hr⟩ := or_operands_unique (os ▸ L.atIndex i) g'
  exact ⟨⟨i,os,Or.inl hl⟩,⟨i,os,Or.inr hr⟩⟩

/-- A path entering a concrete OR tree comes from its own raw leaf, or
    through a named external wire consumed by an actual physical OR. -/
private theorem tree_trace (t : Tree) (checked : t.Checked C n)
    (p : OrPath L x t.out) (top : ∀ w, t = Tree.external w → ReadsOR L w) :
    x.val ∈ t.raws ∨ ∃ w ∈ t.exts, ReadsOR L w ∧ OrPath L x w := by
  induction t with
  | raw j =>
    have e := raw_origin checked p
    exact Or.inl (by simp [Tree.raws,Tree.out] at e ⊢; exact e.symm)
  | external j => exact Or.inr ⟨j,by simp [Tree.exts],top j rfl,p⟩
  | join j l r ihl ihr =>
    obtain ⟨g,cl,cr⟩ := checked
    obtain ⟨rl,rr⟩ := join_reader (L := L) g
    rcases invert_path g p with pl | pr
    · rcases ihl cl pl (fun w eq => by subst l; exact rl) with h | ⟨w,hw,rd,hp⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨w,List.mem_append_left _ hw,rd,hp⟩
    · rcases ihr cr pr (fun w eq => by subst r; exact rr) with h | ⟨w,hw,rd,hp⟩
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr ⟨w,List.mem_append_right _ hw,rd,hp⟩

private theorem path_op {i : T2OrPartition.Id C} (p : OrPath L x (n+i.val)) : L.op i = .or := by
  generalize wi : n+i.val = w at p
  cases p with
  | raw => have := x.isLt; omega
  | @left j op _ => have h : j=i := Fin.ext (by omega); exact h ▸ op
  | @right j op _ => have h : j=i := Fin.ext (by omega); exact h ▸ op

private theorem root_trace (i : T2OrPartition.Id C) (stop : T2OrPartition.next C n i = none)
    (p : OrPath L x (n+i.val)) :
    i ∈ endpoints L x ∨ ∃ w ∈ (makeBlock L Fin.val i).exts, ReadsOR L w ∧ OrPath L x w := by
  have op := path_op p
  let g : GateAt C n (n+i.val) .or (L.left i) (L.right i) := op ▸ L.atIndex i
  let t := (root C n (n+i.val) (L.left i) (L.right i) g).val
  have mb : makeBlock L Fin.val i = Block.group i.val t := by
    unfold makeBlock
    split
    · rename_i eq; simp [op] at eq
    · rfl
  have ans := tree_trace (L := L) t (root C n _ _ _ g).property.2
    (show OrPath L x t.out from p)
    (fun w eq => by simp [t,root] at eq)
  rcases ans with raw | ext
  · exact Or.inl (by simp [endpoints,labels,stop,mb,rawList,raw])
  · exact Or.inr (by simpa only [mb,Block.exts] using ext)

/-- Unshared raw-bearing roots whose only readers are ANDs cannot be upstream
    of any OR reader through an OR-only path from that raw. -/
theorem endpoint_origin (reg : MeetsInternal L)
    (quiet : ∀ i ∈ endpoints L x, T2OrPartition.next C n i = none → OrPath L x (n+i.val) → ¬ ReadsOR L (n+i.val))
    (i : T2OrPartition.Id C) (stop : T2OrPartition.next C n i = none)
    (p : OrPath L x (n+i.val)) : i ∈ endpoints L x := by
  have main (k : Nat) : ∀ j : T2OrPartition.Id C, j.val=k →
      T2OrPartition.next C n j=none → OrPath L x (n+j.val) → j ∈ endpoints L x := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro j jk js jp
      rcases root_trace j js jp with good | ⟨w,hw,rd,walk⟩
      · exact good
      · obtain ⟨⟨d,ds,wd⟩,lt⟩ := root_externals L reg Fin.val j w hw
        subst w
        have good := ih d.val (by omega) d rfl ds walk
        exact False.elim (quiet d good ds walk rd)
  exact main i.val i rfl stop p

theorem covers_of_endpoint_ports (reg : MeetsInternal L) (p : TwoPins (T2OrPartition.Id C))
    (quiet : ∀ r ∈ endpoints L x, T2OrPartition.next C n r = none → OrPath L x (n+r.val) → ¬ ReadsOR L (n+r.val))
    (assigned : ∀ r ∈ endpoints L x, ∀ i, L.op i=.and → ∀ b, port L i b=n+r.val → Hits p i b) :
    CoversPorts L x p := by
  intro i op b walk
  have mem : port L i b ∈ (makeBlock L Fin.val i).exts := by
    unfold makeBlock
    split
    · cases b <;> simp [Block.exts,port]
    · rename_i eq; simp [op] at eq
  obtain ⟨⟨r,stop,wd⟩,_⟩ := root_externals L reg Fin.val i _ mem
  exact assigned r (endpoint_origin reg quiet r stop (wd ▸ walk)) i op b wd

theorem quiet_of_unshared (correct : Computes n C)
    (avoid : ∀ r ∈ endpoints L x, r ∉ ThresholdSharedOrBudget.sharedOrs C n)
    (r : T2OrPartition.Id C) (mem : r ∈ endpoints L x) (stop : T2OrPartition.next C n r=none)
    (p : OrPath L x (n+r.val)) : ¬ReadsOR L (n+r.val) := by
  rintro ⟨j,jop,portEq⟩
  have ro := (physical_op L r).mpr (path_op p)
  have jo := (physical_op L j).mpr jop
  have nout : C.output ≠ n+r.val := by
    intro eq
    have lit := p.lit
    rw [← eq] at lit
    have impossible := (correct {x}).mp lit
    simp at impossible
  have reader : j ∈ T2OrPartition.readers C (n+r.val) := by
    apply T2OrPartition.read_mem
    rw [layout_inputs (L.atIndex j)]
    rcases portEq with e | e <;> simp [e]
  have small : (T2OrPartition.readers C (n+r.val)).length < 2 := by
    by_contra! big
    exact avoid r mem (by simp [ThresholdSharedOrBudget.sharedOrs,ThresholdSharedOrBudget.sharedGates,ro,big])
  have single : T2OrPartition.readers C (n+r.val) = [j] := by
    cases h : T2OrPartition.readers C (n+r.val) with
    | nil => simp [h] at reader
    | cons a tail =>
      cases tail with
      | nil => have eq : j=a := by simpa [h] using reader
               simp [eq]
      | cons b tail => simp [h] at small
  have lt : r<j := by
    rcases portEq with e | e
    · have z := (L.atIndex j).leftEarlier; rw [e] at z; exact Nat.lt_of_add_lt_add_left z
    · have z := (L.atIndex j).rightEarlier; rw [e] at z; exact Nat.lt_of_add_lt_add_left z
  simp [T2OrPartition.next,single,ro,jo,nout,lt] at stop

end ThresholdFirstActive
