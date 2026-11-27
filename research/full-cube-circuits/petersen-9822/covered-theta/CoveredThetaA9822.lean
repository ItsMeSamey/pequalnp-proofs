import OR9822Classification
import OR9822Cofactors

/- BEGIN OR9822Theta233Floor.lean -/
namespace Research.OddOr
open FreeAndNet Theta
namespace Theta233
abbrev I := Fin 5
def target (x : Row I) : Bool :=
  (x.l && (x.raw 0)) || ((x.raw 0) && x.r) || (x.l && (x.raw 1)) || ((x.raw 1) && (x.raw 2)) || ((x.raw 2) && x.r) || (x.l && (x.raw 3)) || ((x.raw 3) && (x.raw 4)) || ((x.raw 4) && x.r)

def low (bits : Nat) : Row I := ⟨bits.testBit 0,bits.testBit 1,fun i => bits.testBit (i.val+2)⟩
def index (p : Tiny I) : Nat :=
  p.1.elim 0 (fun i => i.val+1) * 5 + match p.2 with
  | .unit => 0 | .left => 1 | .right => 2 | .both => 3 | .either => 4

private def witnessChoices : Array (List Nat) := #[[0],[15],[0],[16],[101,50],[1],[17],[62,85],[42,81],[2],[18],[343,170],[241,323],[42,88],[3],[19],[184,325],[81,54],[244,42],[164,323],[4]]
private def witnessCode (p q : Tiny I) : Nat :=
  let a := index p / 5
  let b := index q / 5
  let h := max a b
  let candidates := witnessChoices[h*(h+1)/2 + min a b]?.getD []
  (candidates.find? fun w => decide (Checked target false p q
    ⟨w % 5,Nat.mod_lt _ (by decide)⟩ (low (w / 5)))).getD 0

private def pivotIndex (p q : Tiny I) : I := ⟨witnessCode p q % 5,Nat.mod_lt _ (by decide)⟩
private def pivotRow (p q : Tiny I) : Row I := low (witnessCode p q / 5)

set_option maxRecDepth 16000 in
private theorem cert0 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := (none,e)
    Checked target false p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert1 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 0),e)
    Checked target false p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert2 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 1),e)
    Checked target false p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert3 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 2),e)
    Checked target false p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert4 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 3),e)
    Checked target false p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert5 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 4),e)
    Checked target false p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

private theorem verified (p q : Tiny I) : ∃ i x, Checked target false p q i x := by
  refine ⟨pivotIndex p q,pivotRow p q,?_⟩
  obtain ⟨_ | i,e⟩ := p
  · exact cert0 e q
  · fin_cases i
    · exact cert1 e q
    · exact cert2 e q
    · exact cert3 e q
    · exact cert4 e q
    · exact cert5 e q

private def sparseLow (i j : I) : Row I :=
  low <| match i.val,j.val with
  | 0,0 => 1
  | 0,1 => 1
  | 0,2 => 1
  | 0,3 => 1
  | 0,4 => 1
  | 1,0 => 1
  | 1,1 => 1
  | 1,2 => 1
  | 1,3 => 1
  | 1,4 => 1
  | 2,0 => 8
  | 2,1 => 2
  | 2,2 => 8
  | 2,3 => 8
  | 2,4 => 8
  | 3,0 => 1
  | 3,1 => 1
  | 3,2 => 1
  | 3,3 => 1
  | 3,4 => 1
  | 4,0 => 32
  | 4,1 => 32
  | 4,2 => 32
  | 4,3 => 2
  | 4,4 => 32
  | _,_ => 0

private theorem sparseChecks : ∀ i j : I, i ≠ j →
    let x := sparseLow i j
    target x ≠ target (bump i x) ∧ x.raw j = false ∧ (bump i x).raw j = false := by decide +kernel

private theorem sparse : SparsePivot target := by
  intro i j ne
  exact ⟨sparseLow i j,bump i (sparseLow i j),bump_varies _ _,sparseChecks i j ne⟩

private theorem allPivots (i : I) : ∃ x y, VariesOnly i x y ∧ target x ≠ target y := by
  have other : ∀ z : I, ∃ j : I, z ≠ j := by decide
  obtain ⟨j,ne⟩ := other i
  obtain ⟨x,y,delta,diff,_,_⟩ := sparse i j ne
  exact ⟨x,y,delta,diff⟩

private def otherEdge (i : I) : Row I := low <| match i.val with
  | 0 => 9
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | _ => 0

private theorem residual (i : I) : ∃ z, z.raw i = false ∧ target z = true := by
  have h : ∀ i : I, (otherEdge i).raw i = false ∧ target (otherEdge i) = true := by decide
  exact ⟨_,h i⟩

private theorem census : ∀ a b : Term I, (a.support ≠ ∅ ∨ b.support ≠ ∅) →
    CoversPivots target a b → Survivor target a b := by
  apply classify_small target sparse
  apply small_from_checked _ verified
  intro h; cases h

theorem lower (t : Net V) (h : ∀ s, sees t s = f s) : 7 ≤ t.cost := by
  refine theta_lower f data target ?_ ?_ ?_ allPivots residual census t h
  · intro x
    simp [target,f,fromRow,initial,val,Ep.eval]
  · intro i
    fin_cases i
    · exact price2
    · exact price3
    · exact price4
    · exact price5
    · exact price6
  · constructor
    · decide
    · constructor <;> decide
end Theta233
end Research.OddOr
/- END OR9822Theta233Floor.lean -/

/- BEGIN OR9822Theta144Floor.lean -/
namespace Research.OddOr
open FreeAndNet Theta
namespace Theta144
abbrev I := Fin 6
def target (x : Row I) : Bool :=
  (x.l && x.r) || (x.l && (x.raw 0)) || ((x.raw 0) && (x.raw 1)) || ((x.raw 1) && (x.raw 2)) || ((x.raw 2) && x.r) || (x.l && (x.raw 3)) || ((x.raw 3) && (x.raw 4)) || ((x.raw 4) && (x.raw 5)) || ((x.raw 5) && x.r)

def low (bits : Nat) : Row I := ⟨bits.testBit 0,bits.testBit 1,fun i => bits.testBit (i.val+2)⟩
def index (p : Tiny I) : Nat :=
  p.1.elim 0 (fun i => i.val+1) * 5 + match p.2 with
  | .unit => 0 | .left => 1 | .right => 2 | .both => 3 | .either => 4

private def witnessChoices : Array (List Nat) := #[[0],[48,6,60],[0],[25,37,103],[25,48],[1],[50,14,56],[48,38],[50,25],[2],[387,9,399],[240,387],[217,57],[50,105],[3],[196,208,778],[220,48],[244,25],[292,50],[196,387],[4],[389,17,395],[48,41],[793,65],[485,50],[387,209],[389,196],[5]]
private def witnessCode (p q : Tiny I) : Nat :=
  let a := index p / 5
  let b := index q / 5
  let h := max a b
  let candidates := witnessChoices[h*(h+1)/2 + min a b]?.getD []
  (candidates.find? fun w => decide (Checked target true p q
    ⟨w % 6,Nat.mod_lt _ (by decide)⟩ (low (w / 6)))).getD 0

private def pivotIndex (p q : Tiny I) : I := ⟨witnessCode p q % 6,Nat.mod_lt _ (by decide)⟩
private def pivotRow (p q : Tiny I) : Row I := low (witnessCode p q / 6)

set_option maxRecDepth 16000 in
private theorem cert0 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := (none,e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert1 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 0),e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert2 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 1),e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert3 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 2),e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert4 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 3),e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert5 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 4),e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

set_option maxRecDepth 16000 in
private theorem cert6 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 5),e)
    Checked target true p q (pivotIndex p q) (pivotRow p q) := by decide +kernel

private theorem verified (p q : Tiny I) : ∃ i x, Checked target true p q i x := by
  refine ⟨pivotIndex p q,pivotRow p q,?_⟩
  obtain ⟨_ | i,e⟩ := p
  · exact cert0 e q
  · fin_cases i
    · exact cert1 e q
    · exact cert2 e q
    · exact cert3 e q
    · exact cert4 e q
    · exact cert5 e q
    · exact cert6 e q

private def sparseLow (i j : I) : Row I :=
  low <| match i.val,j.val with
  | 0,0 => 1
  | 0,1 => 1
  | 0,2 => 1
  | 0,3 => 1
  | 0,4 => 1
  | 0,5 => 1
  | 1,0 => 16
  | 1,1 => 4
  | 1,2 => 4
  | 1,3 => 4
  | 1,4 => 4
  | 1,5 => 4
  | 2,0 => 8
  | 2,1 => 2
  | 2,2 => 8
  | 2,3 => 8
  | 2,4 => 8
  | 2,5 => 8
  | 3,0 => 1
  | 3,1 => 1
  | 3,2 => 1
  | 3,3 => 1
  | 3,4 => 1
  | 3,5 => 1
  | 4,0 => 32
  | 4,1 => 32
  | 4,2 => 32
  | 4,3 => 128
  | 4,4 => 32
  | 4,5 => 32
  | 5,0 => 64
  | 5,1 => 64
  | 5,2 => 64
  | 5,3 => 64
  | 5,4 => 2
  | 5,5 => 64
  | _,_ => 0

private theorem sparseChecks : ∀ i j : I, i ≠ j →
    let x := sparseLow i j
    target x ≠ target (bump i x) ∧ x.raw j = false ∧ (bump i x).raw j = false := by decide +kernel

private theorem sparse : SparsePivot target := by
  intro i j ne
  exact ⟨sparseLow i j,bump i (sparseLow i j),bump_varies _ _,sparseChecks i j ne⟩

private theorem allPivots (i : I) : ∃ x y, VariesOnly i x y ∧ target x ≠ target y := by
  have other : ∀ z : I, ∃ j : I, z ≠ j := by decide
  obtain ⟨j,ne⟩ := other i
  obtain ⟨x,y,delta,diff,_,_⟩ := sparse i j ne
  exact ⟨x,y,delta,diff⟩

private def otherEdge (i : I) : Row I := low <| match i.val with
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | _ => 0

private theorem residual (i : I) : ∃ z, z.raw i = false ∧ target z = true := by
  have h : ∀ i : I, (otherEdge i).raw i = false ∧ target (otherEdge i) = true := by decide
  exact ⟨_,h i⟩

private theorem census : ∀ a b : Term I, (a.support ≠ ∅ ∨ b.support ≠ ∅) →
    CoversPivots target a b → Survivor target a b := by
  apply classify_small target sparse
  apply small_from_checked _ verified
  intro _ x h
  simp [target,h]

theorem lower (t : Net V) (h : ∀ s, sees t s = f s) : 8 ≤ t.cost := by
  refine theta_lower f data target ?_ ?_ ?_ allPivots residual census t h
  · intro x
    simp [target,f,fromRow,initial,val,Ep.eval]
  · intro i
    fin_cases i
    · exact price2
    · exact price3
    · exact price4
    · exact price5
    · exact price6
    · exact price7
  · constructor
    · decide
    · constructor <;> decide
end Theta144
end Research.OddOr
/- END OR9822Theta144Floor.lean -/

