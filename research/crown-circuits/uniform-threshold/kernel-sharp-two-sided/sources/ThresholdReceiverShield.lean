import ThresholdStarEndpointRows
import ThresholdSharedPairErase
import ThresholdReceiverPortUse
namespace ThresholdReceiverShield
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete T2OrPartition ThresholdSimpleIncidence
open ThresholdSharedFlow ThresholdStarBypass ResidualSurplus
open private earlier from ThresholdOrGroups
open private any_congr from ThresholdStarBypassPhysical
open private rawBound from ThresholdUniqueRaw
theorem book_eq {C : Circuit} {n} (a b : List Bool) (ha : a.length=n) (hb : b.length=n)
    (bs : List Block) (seen : List Nat) (book : Book C n seen bs)
    (D : Nat → Prop)
    (loc : ∀ g∈bs, ¬D g.out → (C.wires a).getD g.out false=(C.wires b).getD g.out false ∨
      (∀ j∈rawList g, a.getD j false=b.getD j false) ∧ ∀ j∈g.exts, ¬D j)
    (agree : ∀ j∈seen, ¬D j → (C.wires a).getD j false=(C.wires b).getD j false) :
    ∀ j∈outputs bs seen, ¬D j → (C.wires a).getD j false=(C.wires b).getD j false := by
  induction bs generalizing seen with
  | nil => exact agree
  | cons g gs ih =>
    obtain ⟨ck,refs,tail⟩ := book
    have out (safe : ¬D g.out) : (C.wires a).getD g.out false=(C.wires b).getD g.out false := by
      rcases loc g (by simp) safe with yes|⟨raw,ext⟩
      · exact yes
      cases g with
      | meet w x y =>
        simp only [Block.out]
        rw [ck.eval a ha,ck.eval b hb]
        exact congrArg₂ _ (agree x (refs x (by simp [Block.exts])) (ext x (by simp [Block.exts]))) (agree y (refs y (by simp [Block.exts])) (ext y (by simp [Block.exts])))
      | group p t =>
        have aa := t.real ck a ha
        have bb := t.real ck b hb
        dsimp only at aa bb
        simp only [Block.out]
        rw [aa,bb]
        apply congrArg₂ (· || ·)
        · apply any_congr
          intro j hj
          have small := (rawBound t ck j hj)
          exact (earlier C.gates a j (by omega)).trans ((raw j hj).trans (earlier C.gates b j (by omega)).symm)
        · exact any_congr _ _ _ (fun j hj => agree j (refs j hj) (ext j hj))
    apply ih (g.out::seen) tail (fun d hd => loc d (by simp [hd]))
    intro j hj
    rcases List.mem_cons.mp hj with rfl|mem
    · exact out
    · exact agree j mem

theorem cannot_add_shield {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (x y : Fin n) (ne : x≠y)
    (D : Finset (Id (source gs out)))
    (shield : D ⊆ endpoints (layout n gs out M.eligible) y)
    (covered : ∀ u∈D, ∀ i∈ThresholdSecondaryReceivers.signature (source gs out) n u,
      ∀ s : Finset (Fin n), x∈s → ((source gs out).wires (vector s)).getD (n+i.val) false=true)
    (already : ∀ i∈endpoints (layout n gs out M.eligible) y, i∉D →
      ((source gs out).wires (vector {x})).getD (n+i.val) false=true) : False := by
  let C := source gs out
  let L := layout n gs out M.eligible
  obtain ⟨inner,twice,obs⟩ := regular_inputs n gs out M.eligible reg
  obtain ⟨book,_,_,_,seen⟩ := physical_book L inner Fin.val twice obs
  let bad := fun w : Nat => ∃ i∈D, w=n+i.val
  have loc (g : Block) (mem : g∈forest L Fin.val) (safe : ¬bad g.out) :
      (C.wires (vector {x})).getD g.out false=(C.wires (vector {x,y})).getD g.out false ∨
        (∀ j∈rawList g, (vector {x}).getD j false=(vector {x,y}).getD j false) ∧ ∀ j∈g.exts, ¬bad j := by
    by_cases crossed : ∃ j∈g.exts, bad j
    · obtain ⟨j,hj,u,hu,rfl⟩ := crossed
      obtain ⟨i,hi,ho⟩ := ThresholdSecondaryReceivers.receiver_use L Fin.val u g mem hj
      left
      rw [ho,covered u hu i hi {x} (by simp),covered u hu i hi {x,y} (by simp)]
    have ext : ∀ j∈g.exts, ¬bad j := fun j h b => crossed ⟨j,h,b⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    by_cases hot : i∈endpoints L y
    · left
      rw [makeBlock_out,already i hot (fun h => safe ⟨i,h,makeBlock_out ..⟩),endpoint_hot L {x,y} y i (by simp) hot]
    · right
      refine ⟨?_,ext⟩
      have stop : (next C n i).isNone=true := (List.mem_filter.mp hi).2
      have stopped : next (source gs out) n i=none := by simpa using stop
      have absent : y.val∉rawList (makeBlock L Fin.val i) := by
        simpa [endpoints,labels,stopped] using hot
      intro j hj
      have nj : j≠y.val := fun h => absent (h ▸ hj)
      simp only [vec_get]
      split
      next h =>
        have diff : (⟨j,h⟩ : Fin n)≠y := fun e => nj (congrArg Fin.val e)
        simp [diff]
      next => rfl
  have output : ¬bad out := by
    rintro ⟨i,hi,eq⟩
    have h := endpoint_hot L {y} y i (by simp) (shield hi)
    rw [←eq] at h
    have impossible := (M.eligible.1 {y}).mp h
    simp at impossible
  have same := book_eq (vector {x}) (vector {x,y}) (by simp [vector]) (by simp [vector]) _ [] book
    bad loc (by simp) _ seen output
  have ytrue := (M.eligible.1 {x,y}).mpr (by simp [ne])
  have xtrue := (M.eligible.1 {x}).mp (same.trans ytrue)
  simp at xtrue

end ThresholdReceiverShield
