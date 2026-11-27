import Research.CircuitRewire
import Mathlib.Data.Finset.Card
namespace IncidenceResidualCut
open CircuitRewire
variable {m : ℕ}
abbrev Mask (m : ℕ) := Finset (Fin m)

structure Model (m : ℕ) where
  s : ℕ
  out : ℕ
  g : ℕ→Gate
  X : ℕ→Set (Mask m)
  outBound : out<m+s
  earlier : ∀ j<s,(g j).left<m+j ∧ (g j).right<m+j
  raw : ∀ (i : Fin m) A,A∈X i.val ↔ i∈A
  law : ∀ j<s,X (m+j)=(g j).eval X
  bin : ∀ j<s,(g j).op=.join ∨ (g j).op=.meet

def port (g : Gate) (b : Bool) := if b then g.left else g.right

structure Path (C : Model m) (x : Fin m) (v : ℕ) (H : Finset ℕ) : Prop where
  raw : x.val∈H
  last : v∈H
  top : ∀ i∈H,i≤v
  hot : ∀ i∈H,({x}:Mask m)∈C.X i
  boundary : ∀ j<C.s,∀ b,port (C.g j) b∈H → port (C.g j) b=v ∨ m+j∈H

structure Next (C : Model m) (v j : ℕ) (b : Bool) : Prop where
  valid : j<C.s
  read : port (C.g j) b=v
  only : ∀ t<C.s,∀ d,port (C.g t) d=v → t=j ∧ d=b

theorem mono (C : Model m) (i : ℕ) (hi : i<m+C.s) {A B : Mask m} (h : A⊆B) :
    A∈C.X i → B∈C.X i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases lo : i<m
    · exact fun on=>(C.raw ⟨i,lo⟩ B).2 (h ((C.raw ⟨i,lo⟩ A).1 on))
    let j:=i-m
    have e : i=m+j := by dsimp [j]; omega
    have js : j<C.s := by omega
    have ⟨hl,hr⟩ := C.earlier j js
    have l := ih (C.g j).left (by omega) (by omega)
    have r := ih (C.g j).right (by omega) (by omega)
    rw [e,C.law j js]
    rcases C.bin j js with op|op <;> simp only [Gate.eval,op,Op.eval,Set.mem_union,Set.mem_inter_iff] <;> tauto

theorem cut (C : Model m) (x : Fin m) {v j : ℕ} {b : Bool} {H : Finset ℕ}
    (p : Path C x v H) (q : Next C v j b) (A B : Mask m)
    (flip : ∀ i≠x,i∈A ↔ i∈B) (lim : ℕ)
    (exit : m+j<lim → (A∈C.X (m+j) ↔ B∈C.X (m+j))) :
    ∀ i<m+C.s,i<lim → i∉H → (A∈C.X i ↔ B∈C.X i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro good bound outside
    by_cases lo : i<m
    · let r : Fin m := ⟨i,lo⟩
      have ne : r≠x := by
        intro e; apply outside; change r.val∈H; rw [e]; exact p.raw
      exact (C.raw r A).trans ((flip r ne).trans (C.raw r B).symm)
    let t:=i-m
    have e : i=m+t := by dsimp [t]; omega
    have ts : t<C.s := by omega
    by_cases atExit : t=j
    · rw [e,atExit]; exact exit (by omega)
    have side (d : Bool) : port (C.g t) d∉H := by
      intro h
      have eq := (p.boundary t ts d h).resolve_right (e ▸ outside)
      exact atExit (q.only t ts d eq).1
    obtain ⟨hl,hr⟩ := C.earlier t ts
    have l := ih (C.g t).left (by omega) (by omega) (by omega) (side true)
    have r := ih (C.g t).right (by omega) (by omega) (by omega) (side false)
    rw [e,C.law t ts]
    rcases C.bin t ts with op|op <;> simp only [Gate.eval,op,Op.eval,Set.mem_union,Set.mem_inter_iff] <;> tauto

theorem port_early (C : Model m) (j : ℕ) (hj : j<C.s) (b : Bool) :
    port (C.g j) b<m+j := by cases b; exact (C.earlier j hj).2; exact (C.earlier j hj).1

theorem side_out (C : Model m) (x : Fin m) {v j : ℕ} {b : Bool} {H : Finset ℕ}
    (p : Path C x v H) (q : Next C v j b) : port (C.g j) (!b)∉H := by
  have pre := port_early C j q.valid b
  rw [q.read] at pre
  intro h
  have ne : m+j∉H := fun h=>Nat.not_lt_of_ge (p.top _ h) pre
  have eq := (p.boundary j q.valid (!b) h).resolve_right ne
  have bad := (q.only j q.valid (!b) eq).2
  cases b <;> contradiction

theorem sibling_flip (C : Model m) (x : Fin m) {v j : ℕ} {b : Bool} {H : Finset ℕ}
    (p : Path C x v H) (q : Next C v j b) (A : Mask m) :
    (A∈C.X (port (C.g j) (!b)) ↔ insert x A∈C.X (port (C.g j) (!b))) := by
  have early := port_early C j q.valid (!b)
  have js := q.valid
  exact cut C x p q A (insert x A) (fun i ne=>by simp [ne]) (m+j)
    (fun h=>(Nat.lt_irrefl _ h).elim) _ (by omega) early (side_out C x p q)

theorem erased (C : Model m) (x : Fin m) {v j : ℕ} {b : Bool} {H : Finset ℕ}
    (p : Path C x v H) (q : Next C v j b) (A : Mask m) (neg : ({x}:Mask m)∉C.X C.out)
    (hit : insert x A∈C.X C.out) (off : A∉C.X C.out) :
    ((C.g j).op=.join → A∉C.X (port (C.g j) (!b))) ∧
    ((C.g j).op=.meet → A∈C.X (port (C.g j) (!b))) := by
  have reject (same : A∈C.X (m+j) ↔ insert x A∈C.X (m+j)) : False :=
    off ((cut C x p q A _ (fun i ne=>by simp [ne]) _ (fun _=>same) C.out
      C.outBound C.outBound (fun h=>neg (p.hot _ h))).mpr hit)
  have flip := sibling_flip C x p q A
  constructor
  · intro op h
    apply reject
    have h' := flip.mp h
    rw [C.law j q.valid]
    cases b <;> simp [port] at h h' <;> simp only [Gate.eval,op,Op.eval,Set.mem_union] <;> tauto
  · intro op
    by_contra h
    apply reject
    have h' := fun a=>h (flip.mpr a)
    rw [C.law j q.valid]
    cases b <;> simp [port] at h h' <;> simp only [Gate.eval,op,Op.eval,Set.mem_inter_iff] <;> tauto

#print axioms erased
end IncidenceResidualCut
