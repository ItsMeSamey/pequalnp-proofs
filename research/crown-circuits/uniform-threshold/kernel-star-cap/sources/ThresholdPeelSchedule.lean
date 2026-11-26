import ThresholdPeelNative
import Mathlib.Data.Finset.Basic
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdPinCompiler
open ThresholdRemoteAnchor ThresholdPeelNative
namespace ThresholdPeelSchedule
abbrev Pins (m : Nat) := Finset (Fin m)
def row {m} (s : Pins m) : Row m := fun i => decide (i∈s)
def Match {m} (C : Circuit) (f : Pins m → Bool) (u : Pins m) :=
  ∀ s ⊆ u, C.eval (List.ofFn (row s))=f s

private theorem keep {m} (s : Pins m) (p : Fin m) (h : p∉s) :
    pinFalse (List.ofFn (row s)) p.val=List.ofFn (row s) := by
  apply List.ext_getElem
  · simp [pinFalse]
  · intro i hi hj
    by_cases eq : i=p.val
    · subst i; simp [pinFalse,row,h]
    · simp [pinFalse,List.getElem_set,eq,Ne.symm eq]

private theorem nextMatch {m} {C : Circuit} {f : Pins m → Bool} {u : Pins m}
    (ok : Match C f u) (p : Fin m) (mono : PEqualNP.MetaComplexity.Monotone2 C) :
    Match (restrictFalse C m p.val) f (u.erase p) := by
  intro s sub
  have no : p∉s := fun h => (Finset.mem_erase.mp (sub h)).1 rfl
  have sem := (weak_pin_false C p mono).2.1 (List.ofFn (row s)) (by simp)
  rw [keep s p no] at sem
  exact sem.trans (ok s (sub.trans (Finset.erase_subset _ _)))

private theorem row_insert {m} (s : Pins m) (p : Fin m) :
    row (insert p s)=setBit (row s) p true := by
  funext i
  by_cases eq : i=p <;> simp [row,setBit,eq]

inductive Step (m : Nat) where
  | interior (p : Fin m)
  | remote (a b : Fin m)

def after {m} (u : Pins m) : Step m → Pins m
  | .interior p => u.erase p
  | .remote a b => (u.erase a).erase b

def Ready {m} (f : Pins m → Bool) (u : Pins m) : Step m → Prop
  | .interior p => ∃ x z : Pins m, insert p x ⊆ u ∧ z ⊆ u ∧ p∉x ∧ p∉z ∧
      f x=false ∧ f (insert p x)=true ∧ f z=true
  | .remote a b => a≠b ∧ ∃ x z : Pins m, insert b (insert a x) ⊆ u ∧ z ⊆ u ∧
      a∉x ∧ b∉x ∧ a∉z ∧ b∉z ∧ f x=false ∧ f (insert b (insert a x))=true ∧ f z=true

def ending {m} (u : Pins m) : List (Step m) → Pins m
  | [] => u
  | t::ts => ending (after u t) ts

def Scheduled {m} (f : Pins m → Bool) (u : Pins m) : List (Step m) → Prop
  | [] => True
  | t::ts => Ready f u t ∧ Scheduled f (after u t) ts

theorem one {m} (f : Pins m → Bool) (u : Pins m) (t : Step m)
    (ready : Ready f u t) (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (ok : Match C f u) : ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      Match D f (after u t) ∧ ors D.gates+1≤ors C.gates := by
  cases t with
  | interior p =>
    obtain ⟨x,z,sub,zsub,px,pz,fx,fp,fz⟩ := ready
    have flip := (ok _ sub).trans fp
    rw [row_insert] at flip
    have w := ThresholdRemoteAnchor.interior (fun a => C.eval (List.ofFn a)) p (row x)
      (setBit (row x) p true) (row z) (by simp [row,px]) rfl
      ((ok x ((Finset.subset_insert _ _).trans sub)).trans fx)
      flip (by simp [row,pz]) ((ok z zsub).trans fz)
    have charge := witness_minor C p mono w
    exact ⟨_,charge.1,nextMatch ok p mono,charge.2.2⟩
  | remote a b =>
    obtain ⟨ab,x,z,sub,zsub,ax,bx,az,bz,fx,fp,fz⟩ := ready
    have flip := (ok _ sub).trans fp
    rw [row_insert,row_insert] at flip
    have w := anchor_witness (fun s => C.eval (List.ofFn s)) (row x) (row z) a b ab
      (by simp [row,ax]) (by simp [row,bx])
      ((ok x (((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)).trans sub)).trans fx)
      flip (by simp [row,az]) (by simp [row,bz]) ((ok z zsub).trans fz)
    rcases w with wa | wb
    · have c := witness_minor C a mono wa
      have d := weak_pin_false (restrictFalse C m a.val) b c.1
      exact ⟨_,d.1,nextMatch (nextMatch ok a mono) b c.1,by have := c.2.2; have := d.2.2; omega⟩
    · have c := witness_minor C b mono wb
      have d := weak_pin_false (restrictFalse C m b.val) a c.1
      refine ⟨_,d.1,?_,by have := c.2.2; have := d.2.2; omega⟩
      have swap : (u.erase a).erase b=(u.erase b).erase a := by
        ext i; simp [and_left_comm]
      simpa only [after,swap] using nextMatch (nextMatch ok b mono) a c.1

theorem peel {m} {f : Pins m → Bool} (ts : List (Step m)) (u : Pins m)
    (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C) (ok : Match C f u)
    (sched : Scheduled f u ts) : ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      Match D f (ending u ts) ∧ ors D.gates+ts.length≤ors C.gates := by
  induction ts generalizing u C with
  | nil => exact ⟨C,mono,ok,by simp⟩
  | cons t ts ih =>
    obtain ⟨D,dm,agree,cost⟩ := one f u t sched.1 C mono ok
    obtain ⟨E,em,done,total⟩ := ih _ D dm agree sched.2
    exact ⟨E,em,done,by simp only [List.length_cons]; omega⟩
end ThresholdPeelSchedule
