import ThresholdOrWeight
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction
def blockTree : Block → Tree
  | .meet p _ _ => .external p
  | .group _ t => t

noncomputable def trees {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :=
  (forest layout pin).map blockTree

theorem forest_ids {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :
    (trees layout pin).flatMap Tree.gates = allGates (forest layout pin) := by
  unfold trees allGates
  rw [List.flatMap_map]
  congr 1
  funext b
  cases b <;> rfl

theorem trees_balanced {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (q : Nat) (weight : Nat → Nat)
    (law : ∀ p x y, GateAt C n p .or x y →
      atRoot q (branch C n p x).val + atRoot q (branch C n p y).val = weight p) :
    ∀ t∈trees layout pin, Balanced q weight t := by
  intro t ht
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  unfold makeBlock
  split
  · trivial
  · rename_i h
    exact root_balanced layout q weight law _ _ _ (h ▸ layout.atIndex i)

theorem top_block {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (q : Nat) (i : T2OrPartition.Id C) :
    atRoot q (blockTree (makeBlock layout pin i)) =
      if layout.op i=.or ∧ n+i.val=q then 1 else 0 := by
  unfold makeBlock
  split <;> rename_i eq
  · simp [blockTree,atRoot,eq]
  · simp [blockTree,root,atRoot,eq]

theorem all_private_balance {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) {i : T2OrPartition.Id C}
    {j : {j : T2OrPartition.Id C // i<j}} (edge : T2OrPartition.next C n i = some j) :
    (allGates (forest layout pin)).count (n+i.val) = (allGates (forest layout pin)).count (n+j.val.val) := by
  rw [←forest_ids]
  apply private_balance
  · exact trees_balanced layout pin _ _ (private_slot_weight layout edge)
  · intro t ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb
    rw [top_block]
    have ks : T2OrPartition.next C n k=none := by simpa [fixed] using hk
    have ne : n+k.val≠n+i.val := by
      intro eq
      have ki : k=i := Fin.ext (by omega)
      subst k; rw [edge] at ks; contradiction
    simp only [ne,and_false,ite_false]

theorem all_root_balance {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C)
    (stop : T2OrPartition.next C n i=none) :
    (allGates (forest layout pin)).count (n+i.val) = if layout.op i=.or then 1 else 0 := by
  rw [←forest_ids,root_balance (n+i.val) (trees layout pin) (trees_balanced layout pin _ _
    (fun p x y _ => by rw [top_stopped stop,top_stopped stop]))]
  have point (k : T2OrPartition.Id C) :
      atRoot (n+i.val) (blockTree (makeBlock layout pin k)) =
        if layout.op i=.or then (if k=i then 1 else 0) else 0 := by
    rw [top_block]
    by_cases eq : k=i
    · subst k; simp
    · have ne : n+k.val≠n+i.val := by intro h; exact eq (Fin.ext (by omega))
      simp only [eq,ne,ite_false,and_false]; split <;> rfl
  have calcSum (xs : List (T2OrPartition.Id C)) :
      (((xs.map (makeBlock layout pin)).map blockTree).map (atRoot (n+i.val))).sum =
        if layout.op i=.or then xs.count i else 0 := by
    induction xs with
    | nil => simp
    | cons k ks ih =>
      simp only [List.map_cons,List.sum_cons,point,ih]
      by_cases op : layout.op i=.or <;> by_cases eq : k=i <;> simp [op,eq,Nat.add_comm]
  change ((((fixed C n).map (makeBlock layout pin)).map blockTree).map (atRoot (n+i.val))).sum = _
  rw [calcSum]
  have mem : i∈fixed C n := by simp [fixed,stop]
  have nd : (fixed C n).Nodup := (List.nodup_finRange _).filter _
  rw [List.count_eq_one_of_mem nd mem]

theorem physical_count {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) :
    (allGates (forest layout pin)).count (n+i.val) = if layout.op i=.or then 1 else 0 := by
  let count := fun d : T2OrPartition.Id C => (allGates (forest layout pin)).count (n+d.val)
  let m := fun d : T2OrPartition.Id C => count d + (if layout.op d=.or then 0 else 1)
  have each := owner_count (C:=C) (n:=n) m (fun d stop => by
    dsimp [m,count]
    rw [all_root_balance layout pin d stop]
    split <;> simp_all) (fun d j e => by
      have ds := (physical_op layout d).mp (next_is_or e).1
      have js := (physical_op layout j.val).mp (next_is_or e).2
      simpa [m,count,ds,js] using all_private_balance layout pin e) i
  dsimp [m,count] at each
  by_cases h : layout.op i=.or <;> simp [h] at * <;> omega

theorem tree_range {C : Circuit} {n : Nat} (t : Tree) (chk : t.Checked C n) :
    ∀ w∈t.gates, ∃ i : T2OrPartition.Id C, w=n+i.val := by
  induction t with
  | raw | external => simp [Tree.gates]
  | join j l r il ir =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|tail
    · obtain ⟨pre,post,eq,idx⟩ := chk.1.layout
      refine ⟨⟨pre.length,by rw [eq]; simp⟩,idx⟩
    · exact (List.mem_append.mp tail).elim (il chk.2.1 w) (ir chk.2.2 w)

theorem forest_range {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :
    ∀ w∈allGates (forest layout pin), ∃ i : T2OrPartition.Id C, w=n+i.val := by
  intro w hw
  obtain ⟨b,hb,read⟩ := List.mem_flatMap.mp hw
  have chk := forest_checked layout pin b hb
  cases b with
  | meet => simp [Block.orIDs] at read
  | group p t => exact tree_range t chk w read

theorem forest_nodup {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) : (allGates (forest layout pin)).Nodup := by
  apply List.nodup_iff_count_eq_one.mpr
  intro w hw
  obtain ⟨i,rfl⟩ := forest_range layout pin w hw
  have pos := List.count_pos_iff.mpr hw
  have cnt := physical_count layout pin i
  split at cnt <;> omega

#print axioms forest_nodup
end ThresholdOrExtraction
