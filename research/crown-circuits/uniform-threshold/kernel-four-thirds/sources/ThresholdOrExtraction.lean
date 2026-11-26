import ThresholdOrGroups
import T2OrPartition

namespace ThresholdOrExtraction
open PEqualNP.CircuitLowerBounds ThresholdOrGroups

/-- Expose a physical OR producer only at its sole parent, whenever its operands
    are valid earlier wires. At the root the caller supplies the physical OR. -/
noncomputable def branch (C : Circuit) (n parent w : Nat) :
    {t : Tree // t.out = w ∧ t.Checked C n} := by
  classical
  by_cases raw : w < n
  · exact ⟨.raw w,rfl,raw⟩
  by_cases expand : ∃ i : T2OrPartition.Id C, w=n+i.val ∧
      (∃ j : {j : T2OrPartition.Id C // i<j},
           T2OrPartition.next C n i = some j ∧ parent=n+j.val.val) ∧
      ∃ x y, GateAt C n w .or x y
  · let i := expand.choose
    let hx := expand.choose_spec.2.2
    let x := hx.choose
    let y := hx.choose_spec.choose
    have gate : GateAt C n w .or x y := hx.choose_spec.choose_spec
    let l := branch C n w x
    let r := branch C n w y
    exact ⟨.join w l.val r.val,rfl,by
      change GateAt C n w .or l.val.out r.val.out ∧ _ ∧ _
      rw [l.property.1,r.property.1]
      exact ⟨gate,l.property.2,r.property.2⟩⟩
  · exact ⟨.external w,rfl,True.intro⟩
termination_by w
decreasing_by all_goals first | exact gate.leftEarlier | exact gate.rightEarlier

noncomputable def root (C : Circuit) (n w x y : Nat) (gate : GateAt C n w .or x y) :
    {t : Tree // t.out=w ∧ t.Checked C n} :=
  let l := branch C n w x
  let r := branch C n w y
  ⟨.join w l.val r.val,rfl,by
    change GateAt C n w .or l.val.out r.val.out ∧ _ ∧ _
    rw [l.property.1,r.property.1]
    exact ⟨gate,l.property.2,r.property.2⟩⟩
/-- Count an immediate internal child at either side, preserving multiplicity. -/
def atRoot (q : Nat) : Tree → Nat
  | .raw _ | .external _ => 0
  | .join j .. => if j=q then 1 else 0

def childHits (q : Nat) : Tree → Nat
  | .raw _ | .external _ => 0
  | .join _ a b => atRoot q a + atRoot q b + childHits q a + childHits q b

theorem occurrences_split (q : Nat) (t : Tree) :
    t.gates.count q = atRoot q t + childHits q t := by
  induction t with
  | raw i => simp [Tree.gates,atRoot,childHits]
  | external i => simp [Tree.gates,atRoot,childHits]
  | join j a b ha hb =>
    by_cases eq : j=q
    · subst j
      simp [Tree.gates,atRoot,childHits,List.count_cons,ha,hb]
      <;> omega
    · simp [Tree.gates,atRoot,childHits,List.count_cons,eq,ha,hb]
      <;> omega

/-- Repeated joins, including two equal child wires, are charged per slot. -/
def Balanced (q : Nat) (weight : Nat → Nat) : Tree → Prop
  | .raw _ | .external _ => True
  | .join j a b => atRoot q a + atRoot q b = weight j ∧
      Balanced q weight a ∧ Balanced q weight b

theorem childHits_sum (q : Nat) (weight : Nat → Nat) (t : Tree)
    (ok : Balanced q weight t) : childHits q t = (t.gates.map weight).sum := by
  induction t with
  | raw i => rfl
  | external i => rfl
  | join j a b ha hb =>
    rcases ok with ⟨here,left,right⟩
    simp only [childHits,here,ha left,hb right,Tree.gates,List.map_cons,List.map_append,
      List.sum_cons,List.sum_append]
    omega

/-- Multiplicity of private i equals multiplicity of its unique reader j
    when every reader occurrence expands its mandatory slot. -/
theorem private_balance (i j : Nat) (trees : List Tree)
    (inner : ∀ t∈trees, Balanced i (fun k => if k=j then 1 else 0) t)
    (noRoot : ∀ t∈trees, atRoot i t = 0) :
    (trees.flatMap Tree.gates).count i = (trees.flatMap Tree.gates).count j := by
  have countSum (xs : List Nat) :
      (xs.map (fun k => if k=j then 1 else 0)).sum = xs.count j := by
    induction xs with
    | nil => rfl
    | cons k ks ih =>
      by_cases eq : k=j
      · subst k; simp [ih,Nat.add_comm]
      · simp [eq, ih]
  induction trees with
  | nil => rfl
  | cons t ts ih =>
    have eq := occurrences_split i t
    rw [noRoot t (by simp),Nat.zero_add,childHits_sum i _ t (inner t (by simp)),countSum] at eq
    simp only [List.flatMap_cons,List.count_append,eq]
    rw [ih (fun u hu => inner u (by simp [hu])) (fun u hu => noRoot u (by simp [hu]))]

theorem root_balance (i : Nat) (trees : List Tree)
    (inner : ∀ t∈trees, Balanced i (fun _ => 0) t) :
    (trees.flatMap Tree.gates).count i = (trees.map (atRoot i)).sum := by
  have zeroSum (xs : List Nat) : (xs.map (fun _ => (0:Nat))).sum=0 := by
    induction xs <;> simp_all
  induction trees with
  | nil => rfl
  | cons t ts ih =>
    have eq := occurrences_split i t
    rw [childHits_sum i _ t (inner t (by simp)),zeroSum,Nat.add_zero] at eq
    simp only [List.flatMap_cons,List.count_append,List.map_cons,List.sum_cons,eq]
    rw [ih (fun u hu => inner u (by simp [hu]))]

theorem owner_count {C : Circuit} {n : Nat} (measure : T2OrPartition.Id C → Nat)
    (rootCount : ∀ i, T2OrPartition.next C n i = none → measure i = 1)
    (childCount : ∀ i (j : {j : T2OrPartition.Id C // i<j}),
      T2OrPartition.next C n i = some j → measure i = measure j.val)
    (i : T2OrPartition.Id C) : measure i = 1 := by
  cases h : T2OrPartition.next C n i with
  | none => exact rootCount i h
  | some j =>
    exact (childCount i j h).trans (owner_count measure rootCount childCount j.val)
termination_by C.gates.length-i.val
decreasing_by
  have lt := j.property
  change i.val < j.val.val at lt
  have bd := j.val.isLt
  omega

def rawTop : Tree → Nat | .raw _ => 1 | _ => 0

def RawBalanced (ports : Nat → Nat) : Tree → Prop
  | .raw _ | .external _ => True
  | .join j a b => rawTop a + rawTop b = ports j ∧
      RawBalanced ports a ∧ RawBalanced ports b

theorem raw_count_by_physical (ports : Nat → Nat) (t : Tree)
    (h : RawBalanced ports t) :
    t.raws.length = rawTop t + (t.gates.map ports).sum := by
  induction t with
  | raw i => rfl
  | external i => rfl
  | join j a b ha hb =>
    rcases h with ⟨here,left,right⟩
    change (a.raws ++ b.raws).length = 0 + ((j::(a.gates++b.gates)).map ports).sum
    simp only [List.length_append,ha left,hb right,Tree.gates,
      List.map_cons,List.map_append,List.sum_cons,List.sum_append]
    omega

/-- Physical gate lookup is canonical even though the layout certificate
    witnesses a list split. -/
theorem gate_lookup {C : Circuit} {n w x y : Nat} {o : ResidualSurplus.Op}
    (h : GateAt C n w o x y) :
    C.gates[w-n]? = some (ResidualSurplus.binary o x y) := by
  obtain ⟨⟨xs,ys,lay,id⟩,_,_⟩ := h
  simp [lay,id,List.getElem?_append]

theorem or_operands_unique {C : Circuit} {n w x y x' y' : Nat}
    (h : GateAt C n w .or x y) (h' : GateAt C n w .or x' y') : x=x' ∧ y=y' := by
  have eq := (gate_lookup h).symm.trans (gate_lookup h')
  simpa [ResidualSurplus.binary] using congrArg (fun o : Option Gate => o.map Gate.inputs) eq

structure Layout (C : Circuit) (n : Nat) where
  op : T2OrPartition.Id C → ResidualSurplus.Op
  left : T2OrPartition.Id C → Nat
  right : T2OrPartition.Id C → Nat
  atIndex : ∀ i, GateAt C n (n+i.val) (op i) (left i) (right i)

noncomputable def makeBlock {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) : Block :=
  match e : layout.op i with
  | .and => .meet (n+i.val) (layout.left i) (layout.right i)
  | .or => .group (pin i) (root C n (n+i.val) (layout.left i) (layout.right i)
      (e ▸ layout.atIndex i)).val

theorem makeBlock_checked {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) :
    (makeBlock layout pin i).Checked C n := by
  unfold makeBlock
  split
  · rename_i e
    simpa only [Block.Checked, ←e] using layout.atIndex i
  · rename_i e
    exact (root C n (n+i.val) (layout.left i) (layout.right i) (e ▸ layout.atIndex i)).property.2

theorem makeBlock_out {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) :
    (makeBlock layout pin i).out=n+i.val := by
  unfold makeBlock
  split
  · rfl
  · rfl

def fixed (C : Circuit) (n : Nat) :=
  (List.finRange C.gates.length).filter (fun i => (T2OrPartition.next C n i).isNone)

noncomputable def forest {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) : List Block :=
  (fixed C n).map (makeBlock layout pin)

theorem forest_checked {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (b : Block) (mem : b ∈ forest layout pin) :
    b.Checked C n := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
  exact makeBlock_checked layout pin i

/-- A physical-order inventory suffices to turn local frontier facts into
    the compiler's progressively increasing list of stored block roots. -/
theorem book_of_earlier {C : Circuit} {n : Nat} (bs : List Block) (seen : List Nat)
    (good : ∀ b∈bs, b.Checked C n)
    (ordered : bs.Pairwise fun a b => a.out < b.out)
    (frontier : ∀ b∈bs, ∀ w∈b.exts, w∈seen ∨ ∃ a∈bs, a.out=w ∧ w<b.out) :
    Book C n seen bs := by
  induction bs generalizing seen with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨first,tail⟩ := List.pairwise_cons.mp ordered
    refine ⟨good b (by simp), ?_, ih (b.out::seen) (fun a ha => good a (by simp [ha])) tail ?_⟩
    · intro w hw
      rcases frontier b (by simp) w hw with mem | ⟨a,ha,eq,lt⟩
      · exact mem
      · rcases List.mem_cons.mp ha with eqb|rest
        · subst a; omega
        · have := first a rest; omega
    · intro a ha w hw
      rcases frontier a (by simp [ha]) w hw with mem | ⟨d,hd,eq,lt⟩
      · exact Or.inl (by simp [mem])
      · rcases List.mem_cons.mp hd with eqb|rest
        · subst d; exact Or.inl (by simp [eq])
        · exact Or.inr ⟨d,rest,eq,lt⟩

#print axioms forest_checked
#print axioms private_balance
#print axioms book_of_earlier
end ThresholdOrExtraction
