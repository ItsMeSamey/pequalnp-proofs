import IncidenceHoistRealize
import IncidenceHoistEndpoint
import IncidenceLineRoutedSlots

namespace IncidenceHoistSingleton
open CircuitRewire IncidenceStartNormalization IncidenceHoistCompile IncidenceHoistFlow
open IncidenceHoistRealize IncidenceHoistEndpoint SparseIncidence

private theorem front {Z : Type} {m : Nat} {W : Nat → Set Z} (gs hs : List Gate)
    (h : Models m W (gs++hs)) : Models m W gs := by
  intro i hi
  have eq := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at eq

theorem reference {n : Nat} (C : Circuit n) (sel : Nat → Option Bool) :
    let m := n+n
    let D := circuit C sel
    ∀ i<m+C.size, D.wire ((buildPrefix m C.code sel C.size).ref i)=value C.wire C.code sel m C.size i := by
  let m := n+n
  let Y := value C.wire C.code sel m C.size
  let D := circuit C sel
  let p := buildPrefix m C.code sel C.size
  let gs := codeList m C.size C.output C.code sel
  have len : gs.length=C.size := physical_size ..
  have run : Models m D.wire gs := by
    intro i hi
    have eq := D.law i (by change i<C.size; omega)
    change D.wire (m+i) = (gs.getD i ⟨.zero,0,0⟩).eval D.wire at eq
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using eq
  have raw (i : Nat) (hi : i<m) : D.wire i=Y i := by
    change value C.wire D.code (fun _ => none) m C.size i = Y i
    have d := stable C.wire D.code (fun _ => none) m 0 C.size i (by omega)
    have y := stable C.wire C.code sel m 0 C.size i (by omega)
    simpa only [Nat.zero_add] using d.trans y.symm
  exact (prefix_sem m C.size C.code sel D.wire Y raw C.earlier
    (fun i h => law C.wire C.code sel m C.size i h (C.earlier i h)) (front _ _ run)).1

def Quiet {n} (C : Circuit n) (sel : Nat→Option Bool) (z : Input n) :=
  ∀ j<C.size,∀ b,sel j=some b → z∉C.wire (other (C.code j) b)

theorem agrees {n} (C : Circuit n) (sel : Nat→Option Bool) (z : Input n)
    (joins : ∀ j<C.size,∀ b,sel j=some b → (C.code j).op=.join)
    (quiet : Quiet C sel z) (i : Nat) (hi : i<n+n+C.size) :
    z∈(circuit C sel).wire ((buildPrefix (n+n) C.code sel C.size).ref i) ↔ z∈C.wire i := by
  rw [reference C sel i hi]
  have h := sandwich (n+n) C.size C.wire C.code sel C.earlier C.law joins
  refine ⟨fun x => (h i hi).1 x,?_⟩
  intro old
  rcases (h i hi).2 old with now|⟨j,hj,b,hb,side⟩
  · exact now
  · have ⟨l,r⟩ := C.earlier j hj
    have bound : other (C.code j) b<n+n+C.size := by
      cases b <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
    exact (quiet j hj b hb ((h _ bound).1 side)).elim

theorem agrees_prefix {n} (C : Circuit n) (sel : Nat→Option Bool) (z : Input n)
    (joins : ∀ j<C.size,∀ b,sel j=some b → (C.code j).op=.join)
    (quiet : Quiet C sel z) (j i : Nat) (hj : j≤C.size) (hi : i<n+n+j) :
    z∈(circuit C sel).wire ((buildPrefix (n+n) C.code sel j).ref i) ↔ z∈C.wire i := by
  have h := ref_stable (n+n) C.code sel j (C.size-j) i hi
  rw [show j+(C.size-j)=C.size by omega] at h
  rw [← h]
  exact agrees C sel z joins quiet i (by omega)

#print axioms agrees
#print axioms agrees_prefix
end IncidenceHoistSingleton
