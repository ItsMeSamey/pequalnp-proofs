import ThresholdStarEndpointRows
import ThresholdSharedPairErase
namespace ThresholdAlreadyHot
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete T2OrPartition ThresholdSimpleIncidence
open ThresholdSharedFlow ThresholdStarBypass ResidualSurplus
open private earlier from ThresholdOrGroups
open private any_congr from ThresholdStarBypassPhysical
open private rawBound from ThresholdUniqueRaw
private theorem book_eq {C : Circuit} {n} (a b : List Bool) (ha : a.length=n) (hb : b.length=n)
    (bs : List Block) (seen : List Nat) (book : Book C n seen bs)
    (loc : ∀ g∈bs, (C.wires a).getD g.out false=(C.wires b).getD g.out false ∨
      ∀ j∈rawList g, a.getD j false=b.getD j false)
    (agree : ∀ j∈seen,(C.wires a).getD j false=(C.wires b).getD j false) :
    ∀ j∈outputs bs seen,(C.wires a).getD j false=(C.wires b).getD j false := by
  induction bs generalizing seen with
  | nil => exact agree
  | cons g gs ih =>
    obtain ⟨ck,refs,tail⟩ := book
    have out : (C.wires a).getD g.out false=(C.wires b).getD g.out false := by
      rcases loc g (by simp) with yes|raw
      · exact yes
      cases g with
      | meet w x y =>
        simp only [Block.out]
        rw [ck.eval a ha,ck.eval b hb]
        exact congrArg₂ _ (agree x (refs x (by simp [Block.exts]))) (agree y (refs y (by simp [Block.exts])))
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
        · exact any_congr _ _ _ (fun j hj => agree j (refs j hj))
    apply ih (g.out::seen) tail (fun d hd => loc d (by simp [hd]))
    intro j hj
    rcases List.mem_cons.mp hj with rfl|mem
    · exact out
    · exact agree j mem

theorem cannot_add {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (x y : Fin n) (ne : x≠y)
    (already : ∀ i∈endpoints (layout n gs out M.eligible) y,
      ((source gs out).wires (vector {x})).getD (n+i.val) false=true) : False := by
  let C := source gs out
  let L := layout n gs out M.eligible
  obtain ⟨inner,twice,obs⟩ := regular_inputs n gs out M.eligible reg
  obtain ⟨book,_,_,_,seen⟩ := physical_book L inner Fin.val twice obs
  have loc (g : Block) (mem : g∈forest L Fin.val) :
      (C.wires (vector {x})).getD g.out false=(C.wires (vector {x,y})).getD g.out false ∨
        ∀ j∈rawList g, (vector {x}).getD j false=(vector {x,y}).getD j false := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    by_cases hot : i∈endpoints L y
    · left
      rw [makeBlock_out,already i hot,endpoint_hot L {x,y} y i (by simp) hot]
    · right
      have stop : (next C n i).isNone=true := (List.mem_filter.mp hi).2
      have st : next C n i=none := by simpa using stop
      have absent : y.val∉rawList (makeBlock L Fin.val i) := by
        simpa [endpoints,labels,show next (source gs out) n i=none from st] using hot
      intro j hj
      have nj : j≠y.val := fun h => absent (h ▸ hj)
      simp only [vec_get]
      split
      next h =>
        have diff : (⟨j,h⟩ : Fin n)≠y := fun e => nj (congrArg Fin.val e)
        simp [diff]
      next => rfl
  have same := book_eq (vector {x}) (vector {x,y}) (by simp [vector]) (by simp [vector]) _ [] book
    loc (by simp) _ seen
  have ytrue := (M.eligible.1 {x,y}).mpr (by simp [ne])
  have xtrue := (M.eligible.1 {x}).mp (same.trans ytrue)
  simp at xtrue

theorem no_common_raw {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (x y : Fin n) (ne : x≠y) (U W X : Id (source gs out))
    (ux : U∈endpoints (layout n gs out M.eligible) x)
    (xx : X∈endpoints (layout n gs out M.eligible) x)
    (pair : endpoints (layout n gs out M.eligible) y ⊆ {W,X})
    (act : active (layout n gs out M.eligible) U W=true) : False := by
  let L := layout n gs out M.eligible
  let input := vector ({x} : Finset (Fin n))
  have hu := endpoint_hot L {x} x U (by simp) ux
  have hw := ThresholdSharedPairErase.probe_le_actual L U
    (fun i => ((source gs out).wires input).getD i false)
    (fun i => (L.atIndex i).eval input (by simp [input,vector])) hu _ act
  apply cannot_add M reg x y ne
  intro i hi
  rcases Finset.mem_insert.mp (pair hi) with rfl|h
  · exact hw
  · obtain rfl := Finset.mem_singleton.mp h
    exact endpoint_hot L {x} x _ (by simp) xx
end ThresholdAlreadyHot
