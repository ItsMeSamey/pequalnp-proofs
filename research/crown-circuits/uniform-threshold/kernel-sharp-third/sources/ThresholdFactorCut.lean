import ThresholdFactorReady
import ThresholdFanoutBudget
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction T2OrPartition
open ThresholdFactorForest ThresholdFactorReady
namespace ThresholdFactorCut

private theorem physical {C : Circuit} {n j u v : Nat} {o : Op} (g : GateAt C n j o u v) :
    ∃ i : Id C, j=n+i.val ∧ C.gates.get i=binary o u v := by
  obtain ⟨⟨pre,post,eq,idx⟩,_,_⟩ := g
  let i : Id C := ⟨pre.length,by simp [eq]⟩
  exact ⟨i,idx,by simp [i,eq,List.get_eq_getElem,List.getElem_append_right]⟩

private theorem ext_reader {C : Circuit} {n} (t : Tree) (checked : t.Checked C n) (w : Nat)
    (hit : w∈t.exts) :
    t=.external w ∨ ∃ i : Id C, w∈(C.gates.get i).inputs ∧ (C.gates.get i).op=.or := by
  induction t with
  | raw k => simp [Tree.exts] at hit
  | external k => exact Or.inl (congrArg Tree.external (List.mem_singleton.mp hit).symm)
  | join j l r hl hr =>
    obtain ⟨gate,cl,cr⟩ := checked
    obtain ⟨i,_,g⟩ := physical gate
    right
    rcases List.mem_append.mp hit with left|right
    · rcases hl cl left with e|ex
      · exact ⟨i,by rw [g]; simp [e,binary,Tree.out],by rw [g]; rfl⟩
      · exact ex
    · rcases hr cr right with e|ex
      · exact ⟨i,by rw [g]; simp [e,binary,Tree.out],by rw [g]; rfl⟩
      · exact ex

private theorem unique_consumer {C : Circuit} {w : Nat} {i z : Id C}
    (only : readers C w=[z]) (uses : w∈(C.gates.get i).inputs) : i=z := by
  have inside := read_mem uses
  rw [only] at inside
  exact List.mem_singleton.mp inside

theorem physical_no_other {C : Circuit} {n w : Nat} (L : Layout C n) (pin : Id C → Nat)
    (z : Id C) (andZ : (C.gates.get z).op=.and) (only : readers C w=[z])
    (g : Block) (mem : g∈forest L pin) (elsewhere : g.out≠n+z.val) : w∉g.exts := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
  intro hit
  unfold makeBlock at hit
  split at hit
  next meet =>
    have gate := L.atIndex i
    have ins := layout_inputs gate
    have read : w∈(C.gates.get i).inputs := by rw [ins]; exact hit
    have eq := unique_consumer only read
    exact elsewhere ((makeBlock_out L pin i).trans (by rw [eq]))
  next eq =>
    let gate : GateAt C n (n+i.val) .or (L.left i) (L.right i) := eq ▸ L.atIndex i
    let t := (root C n _ _ _ gate).val
    have h := ext_reader t (root C n _ _ _ gate).property.2 w hit
    rcases h with impossible|⟨d,used,org⟩
    · change Tree.join _ _ _ = Tree.external _ at impossible
      contradiction
    · have equal := unique_consumer only used
      subst d; rw [andZ] at org; contradiction

theorem output_nodup {C : Circuit} {n} (L : Layout C n) (pin : Id C → Nat) :
    ((forest L pin).map Block.out).Nodup := by
  have inj : Function.Injective (fun i : Id C => n+i.val) := fun _ _ h => Fin.ext (Nat.add_left_cancel h)
  have nd : (fixed C n).Nodup := (List.nodup_finRange _).filter _
  simpa [forest,List.map_map,Function.comp_def,makeBlock_out] using nd.map inj

theorem same_and_impossible {C : Circuit} {n x : Nat} (L : Layout C n) (pin : Id C → Nat)
    (internal : MeetsInternal L) (mini : T2SoleOrSplice.LexMinimum n C) (hn : 2≤n)
    (a b : Tree) (p q : Nat) (z : Id C)
    (aa : Block.group p a∈forest L pin) (bb : Block.group q b∈forest L pin)
    (meet : Block.meet (n+z.val) a.out b.out∈forest L pin)
    (xa : x∈a.raws) (xb : x∈b.raws) (hx : x<n) (ab : a.out≠b.out)
    (oa : C.output≠a.out) (ob : C.output≠b.out)
    (ca : readers C a.out=[z]) (cb : readers C b.out=[z]) : False := by
  have checked := forest_checked L pin _ meet
  change GateAt C n (n+z.val) .and a.out b.out at checked
  have gate : C.gates.get z=binary .and a.out b.out := by simpa using gate_lookup checked
  have andZ : (C.gates.get z).op=.and := by rw [gate]; rfl
  apply exclude L pin internal mini hn a b
  exact {
    raw := hx
    left := forest_checked L pin _ aa
    right := forest_checked L pin _ bb
    inLeft := xa
    inRight := xb
    distinct := ab
    leftNotMeet := Nat.ne_of_lt checked.leftEarlier
    rightNotMeet := Nat.ne_of_lt checked.rightEarlier
    unobserved := ⟨oa,ob⟩
    receiver := checked
    exclusive := by
      intro g hg ne j hj
      exact ⟨fun eq => physical_no_other L pin z andZ ca g hg ne (eq ▸ hj),
        fun eq => physical_no_other L pin z andZ cb g hg ne (eq ▸ hj)⟩
    leftIn := ⟨p,aa⟩
    rightIn := ⟨q,bb⟩
    meetIn := meet
    distinctOutputs := output_nodup L pin
  }


theorem same_reader {C : Circuit} {n x : Nat} (L : Layout C n) (pin : Id C → Nat)
    (internal : MeetsInternal L) (mini : T2SoleOrSplice.LexMinimum n C) (hn : 2≤n)
    (a b : Tree) (p q : Nat) (z : Id C) (andZ : L.op z=.and)
    (aa : Block.group p a∈forest L pin) (bb : Block.group q b∈forest L pin)
    (xa : x∈a.raws) (xb : x∈b.raws) (hx : x<n) (ab : a.out≠b.out)
    (oa : C.output≠a.out) (ob : C.output≠b.out)
    (ca : readers C a.out=[z]) (cb : readers C b.out=[z]) : False := by
  have off : T2OrPartition.isOr C z=false := by
    cases flag : T2OrPartition.isOr C z with
    | false => rfl
    | true => have h := (physical_op L z).mp flag; rw [andZ] at h; contradiction
  have stop : T2OrPartition.next C n z=none := by
    unfold T2OrPartition.next
    split <;> simp [off]
  have inBook : Block.meet (n+z.val) (L.left z) (L.right z)∈forest L pin := by
    apply List.mem_map.mpr
    exact ⟨z,List.mem_filter.mpr ⟨List.mem_finRange _,by simp [stop]⟩,by unfold makeBlock; split <;> simp_all⟩
  have options (w : Nat) (read : readers C w=[z]) : w=L.left z ∨ w=L.right z := by
    have use := ThresholdFanoutBudget.reader_pin (C:=C) (w:=w) (j:=z) (by simp [read])
    rw [layout_inputs (L.atIndex z)] at use
    simpa using use
  rcases options a.out ca with al|ar <;> rcases options b.out cb with bl|br
  · exact ab (al.trans bl.symm)
  · rw [←al,←br] at inBook
    exact same_and_impossible L pin internal mini hn a b p q z aa bb inBook xa xb hx ab oa ob ca cb
  · rw [←bl,←ar] at inBook
    exact same_and_impossible L pin internal mini hn b a q p z bb aa inBook xb xa hx ab.symm ob oa cb ca
  · exact ab (ar.trans br.symm)

private theorem original_raw {C : Circuit} (w : List Bool) (i : Nat) (hi : i<w.length) :
    (C.wires w).getD i false=w.getD i false := by
  change (run C.gates w).getD i false=_
  generalize C.gates=gs
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false=_
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem unobserved {C : Circuit} {n} (x : Fin n) (t : Tree)
    (shape : t.Checked C n) (hit : x.val∈t.raws) (rep : T2SoleOrSplice.Computes n C) :
    C.output≠t.out := by
  intro eq
  let w := T2SoleOrSplice.vector ({x} : Finset (Fin n))
  have len : w.length=n := by simp [w,T2SoleOrSplice.vector]
  have on : (C.wires w).getD x.val false=true := by
    rw [original_raw _ _ (by simpa [len] using x.isLt)]
    simp [w,T2SoleOrSplice.vector,List.getD_eq_getElem?_getD,x.isLt]
  have hot : t.raws.any (fun i => (C.wires w).getD i false)=true := List.any_eq_true.mpr ⟨x.val,hit,on⟩
  have rt := t.real shape w len
  dsimp only at rt
  have acc : C.eval w=true := by
    change (C.wires w).getD C.output false=true
    rw [eq,rt,hot]; rfl
  have impossible := (rep {x}).mp acc
  simp at impossible

theorem private_groups_distinct_readers {C : Circuit} {n} (L : Layout C n) (pin : Id C → Nat)
    (internal : MeetsInternal L) (mini : T2SoleOrSplice.LexMinimum n C) (hn : 2≤n)
    (x : Fin n) (a b : Tree) (p q : Nat) (u v : Id C) (andU : L.op u=.and)
    (aa : Block.group p a∈forest L pin) (bb : Block.group q b∈forest L pin)
    (xa : x.val∈a.raws) (xb : x.val∈b.raws) (ab : a.out≠b.out)
    (ru : readers C a.out=[u]) (rv : readers C b.out=[v]) : u≠v := by
  rintro rfl
  exact same_reader L pin internal mini hn a b p q u andU aa bb xa xb x.isLt ab
    (unobserved x a (forest_checked L pin _ aa) xa mini.eligible.1)
    (unobserved x b (forest_checked L pin _ bb) xb mini.eligible.1) ru rv
#print axioms private_groups_distinct_readers
end ThresholdFactorCut
