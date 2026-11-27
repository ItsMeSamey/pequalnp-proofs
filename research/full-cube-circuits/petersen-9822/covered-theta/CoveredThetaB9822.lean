import OR9822Classification
import OR9822Cofactors

/- BEGIN OR9822Theta145Floor.lean -/
namespace Research.OddOr
open FreeAndNet Theta
namespace Theta145
abbrev I := Fin 7
def target (x : Row I) : Bool :=
  (x.l && x.r) || (x.l && (x.raw 0)) || ((x.raw 0) && (x.raw 1)) || ((x.raw 1) && (x.raw 2)) || ((x.raw 2) && x.r) || (x.l && (x.raw 3)) || ((x.raw 3) && (x.raw 4)) || ((x.raw 4) && (x.raw 5)) || ((x.raw 5) && (x.raw 6)) || ((x.raw 6) && x.r)

def low (bits : Nat) : Row I := ⟨bits.testBit 0,bits.testBit 1,fun i => bits.testBit (i.val+2)⟩
def index (p : Tiny I) : Nat :=
  p.1.elim 0 (fun i => i.val+1) * 5 + match p.2 with
  | .unit => 0 | .left => 1 | .right => 2 | .both => 3 | .either => 4

private def witnessChoices : Array (List Nat) := #[[0],[56,7,70],[0],[29,43,120],[29,56],[1],[58,16,65],[56,44],[58,29],[2],[451,10,465],[280,451],[253,66],[58,122],[3],[228,242,907],[256,56],[284,29],[340,58],[228,451],[4],[453,460,467],[481,56],[509,29],[565,58],[2021,451],[453,228],[5],[902,20,909],[56,48],[1821,76],[1014,58],[451,244],[2020,468],[902,453],[6]]
private def witnessCode (p q : Tiny I) : Nat :=
  let a := index p / 5
  let b := index q / 5
  let h := max a b
  let candidates := witnessChoices[h*(h+1)/2 + min a b]?.getD []
  (candidates.find? fun w => decide (Checked target true p q
    ⟨w % 7,Nat.mod_lt _ (by decide)⟩ (low (w / 7)))).getD 0

private def pivotIndex (p q : Tiny I) : I := ⟨witnessCode p q % 7,Nat.mod_lt _ (by decide)⟩
private def pivotRow (p q : Tiny I) : Row I := low (witnessCode p q / 7)

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

set_option maxRecDepth 16000 in
private theorem cert7 : ∀ e : Ep, ∀ q : Tiny I,
    let p : Tiny I := ((some 6),e)
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
    · exact cert7 e q

private def sparseLow (i j : I) : Row I :=
  low <| match i.val,j.val with
  | 0,0 => 1
  | 0,1 => 1
  | 0,2 => 1
  | 0,3 => 1
  | 0,4 => 1
  | 0,5 => 1
  | 0,6 => 1
  | 1,0 => 16
  | 1,1 => 4
  | 1,2 => 4
  | 1,3 => 4
  | 1,4 => 4
  | 1,5 => 4
  | 1,6 => 4
  | 2,0 => 8
  | 2,1 => 2
  | 2,2 => 8
  | 2,3 => 8
  | 2,4 => 8
  | 2,5 => 8
  | 2,6 => 8
  | 3,0 => 1
  | 3,1 => 1
  | 3,2 => 1
  | 3,3 => 1
  | 3,4 => 1
  | 3,5 => 1
  | 3,6 => 1
  | 4,0 => 32
  | 4,1 => 32
  | 4,2 => 32
  | 4,3 => 128
  | 4,4 => 32
  | 4,5 => 32
  | 4,6 => 32
  | 5,0 => 64
  | 5,1 => 64
  | 5,2 => 64
  | 5,3 => 64
  | 5,4 => 256
  | 5,5 => 64
  | 5,6 => 64
  | 6,0 => 128
  | 6,1 => 128
  | 6,2 => 128
  | 6,3 => 128
  | 6,4 => 128
  | 6,5 => 2
  | 6,6 => 128
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
  | 6 => 3
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

theorem lower (t : Net V) (h : ∀ s, sees t s = f s) : 9 ≤ t.cost := by
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
    · exact price8
  · constructor
    · decide
    · constructor <;> decide
end Theta145
end Research.OddOr
/- END OR9822Theta145Floor.lean -/

