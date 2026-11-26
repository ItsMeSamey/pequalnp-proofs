import ThresholdFactorRecipe
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdFactorExpr
namespace ThresholdFactorNetwork

structure Job where
  output : Nat
  term : Term

def valid (n : Nat) : List Nat → List Job → Prop
  | _,[] => True
  | seen,j::js => j.term.Avail n seen ∧ valid n (j.output::seen) js

def seenAfter : List Job → List Nat → List Nat
  | [],seen => seen
  | j::js,seen => seenAfter js (j.output::seen)

structure Work {α : Type} (n : Nat) (raw : α → List Bool) (spec : α → Nat → Bool) (seen : List Nat) where
  gs : List Gate
  ren : Nat → Nat
  mono : Mono gs
  bound : ∀ j∈seen,ren j<n+gs.length
  correct : ∀ j∈seen,∀ a, (run gs (raw a)).getD (ren j) false=spec a j

private theorem sizeRun (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w++[val g w])).length=_
    rw [ih]; simp <;> omega

private theorem prior (gs : List Gate) (w : List Bool) (i : Nat) (lt : i<w.length) :
    (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false=_
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]

theorem program {α : Type} {n : Nat} {raw : α → List Bool} {spec : α → Nat → Bool}
    (arity : ∀ a,(raw a).length=n) (js : List Job) (seen : List Nat) (W : Work n raw spec seen)
    (ok : valid n seen js)
    (localOK : ∀ j∈js,∀ a,j.term.value (fun i => (raw a).getD i false) (spec a)=spec a j.output) :
    ∃ F : Work n raw spec (seenAfter js seen), F.gs.length=W.gs.length+(js.map (fun j => j.term.cost)).sum := by
  induction js generalizing seen with
  | nil => exact ⟨W,by simp⟩
  | cons j js ih =>
    let k := n+W.gs.length
    let add := j.term.build W.ren k
    have d := term_build j.term n seen W.ren (List.replicate k false) ok.1 (by simp [k])
      (fun i hi => by simpa [k] using W.bound i hi)
    simp only [List.length_replicate] at d
    have sem (a : α) : (run add.1 (run W.gs (raw a))).getD add.2 false=spec a j.output := by
      let u := run W.gs (raw a)
      have len : u.length=k := by simp [u,k,sizeRun,arity]
      have compare (t : Term) (av : t.Avail n seen) :
          t.value (fun i => u.getD i false) (fun i => u.getD (W.ren i) false)=
          t.value (fun i => (raw a).getD i false) (spec a) := by
        induction t with
        | raw i => exact prior _ _ _ (by simpa [arity,Term.Avail] using av)
        | ref i => exact W.correct i av a
        | node o l r hl hr => exact congrArg₂ (act o) (hl av.1) (hr av.2)
      have h := term_build j.term n seen W.ren u ok.1 (by rw [len]; dsimp [k]; omega)
        (fun i hi => by rw [len]; exact W.bound i hi)
      rw [len] at h
      exact h.2.2.2.trans ((compare _ ok.1).trans (localOK j (by simp) a))
    let F : Work n raw spec (j.output::seen) := {
      gs := W.gs++add.1
      ren := fun i => if i=j.output then add.2 else W.ren i
      mono := fun g hg => (List.mem_append.mp hg).elim (W.mono g) (d.2.1 g)
      bound := by
        intro i hi
        by_cases eq : i=j.output
        · simpa [eq,k,add,Nat.add_assoc] using d.2.2.1
        · have small := W.bound i (by simpa [eq] using hi)
          simp [eq]; omega
      correct := by
        intro i hi a
        by_cases eq : i=j.output
        · simpa [eq,run,List.foldl_append] using sem a
        · have old : i∈seen := by simpa [eq] using hi
          have lt : W.ren i<(run W.gs (raw a)).length := by simpa [sizeRun,arity] using W.bound i old
          have cut := prior add.1 (run W.gs (raw a)) (W.ren i) lt
          simpa [eq,run,List.foldl_append] using cut.trans (W.correct i old a)
    }
    obtain ⟨out,sz⟩ := ih _ F ok.2 (fun q h => localOK q (by simp [h]))
    exact ⟨out,by simpa [F,add,d.1,Nat.add_assoc] using sz⟩

end ThresholdFactorNetwork
