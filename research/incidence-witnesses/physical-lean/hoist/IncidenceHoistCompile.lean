import IncidenceHoistFlow
namespace IncidenceHoistCompile
open CircuitRewire IncidenceHoistFlow

structure Built where
  kept : List Gate
  siblings : List ℕ
  ref : ℕ → ℕ

def redirect (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,f g.left,f g.right⟩

def buildPrefix (m : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) : ℕ → Built
  | 0 => ⟨[],[],id⟩
  | t+1 =>
    let p := buildPrefix m code sel t
    match sel t with
    | none => ⟨p.kept ++ [redirect p.ref (code t)],p.siblings,
                put p.ref (m+t) (m+p.kept.length)⟩
    | some b => ⟨p.kept,p.siblings ++ [p.ref (other (code t) b)],
                put p.ref (m+t) (p.ref (keep (code t) b))⟩

def appendJoins : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | next, acc, x::xs => ⟨.join,acc,x⟩ :: appendJoins (next+1) next xs

def codeList (m s out : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) :=
  let p := buildPrefix m code sel s
  p.kept ++ appendJoins (m+p.kept.length) (p.ref out) p.siblings

theorem prefix_length (m : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) (t : ℕ) :
    (buildPrefix m code sel t).kept.length + (buildPrefix m code sel t).siblings.length=t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    cases e : sel t <;> simp only [buildPrefix,e,List.length_append,List.length_singleton] <;> omega

theorem append_length (n a : ℕ) (xs : List ℕ) : (appendJoins n a xs).length=xs.length := by
  induction xs generalizing n a with
  | nil => rfl
  | cons x xs ih => simp only [appendJoins,List.length_cons,ih]

theorem physical_size (m s out : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) :
    (codeList m s out code sel).length=s := by
  simp only [codeList,List.length_append,append_length,prefix_length]

def Ordered (m : ℕ) (gs : List Gate) :=
  ∀ i : Fin gs.length, (gs.get i).left<m+i.val ∧ (gs.get i).right<m+i.val

theorem ordered_snoc {m : ℕ} {gs : List Gate} (h : Ordered m gs) (g : Gate)
    (l : g.left<m+gs.length) (r : g.right<m+gs.length) : Ordered m (gs++[g]) := by
  intro i
  by_cases early : i.val < gs.length
  · simpa [List.get_eq_getElem,early] using h ⟨i.val,early⟩
  · have eq : i.val=gs.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
    simpa [List.get_eq_getElem,eq] using And.intro l r

theorem well_prefix (m : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) (t : ℕ)
    (old : ∀ j<t, (code j).left<m+j ∧ (code j).right<m+j) :
    let p := buildPrefix m code sel t
    Ordered m p.kept ∧ (∀ i<m+t, p.ref i<m+p.kept.length) ∧
      (∀ i∈p.siblings, i<m+p.kept.length) := by
  induction t with
  | zero =>
    simp only [buildPrefix,List.length_nil,Nat.add_zero]
    refine ⟨?_,fun _ hi => hi,by simp⟩
    intro i
    exact Fin.elim0 i
  | succ t ih =>
    let p := buildPrefix m code sel t
    obtain ⟨ord,refs,sibs⟩ := ih (fun j hj => old j (by omega))
    have ⟨hl,hr⟩ := old t (by omega)
    cases e : sel t with
    | none =>
      simp only [buildPrefix,e,List.length_append,List.length_singleton]
      refine ⟨ordered_snoc ord _ (refs _ hl) (refs _ hr),?_,?_⟩
      · intro i hi
        by_cases eq : i=m+t
        · simp [put,eq]
        · rw [show put _ (m+t) _ i = (buildPrefix m code sel t).ref i from if_neg eq]
          have := refs i (by omega)
          omega
      · intro i hi
        have := sibs i hi
        omega
    | some b =>
      simp only [buildPrefix,e]
      have main : keep (code t) b<m+t := by cases b <;> simp [keep,hl,hr]
      have side : other (code t) b<m+t := by cases b <;> simp [other,hl,hr]
      refine ⟨ord,?_,?_⟩
      · intro i hi
        by_cases eq : i=m+t
        · simpa [put,eq] using refs _ main
        · simpa [put,eq] using refs i (by omega)
      · intro i hi
        rcases List.mem_append.mp hi with h|h
        · exact sibs i h
        · have eq := List.mem_singleton.mp h
          exact eq ▸ refs _ side

theorem ordered_append {m : ℕ} {gs hs : List Gate}
    (g : Ordered m gs) (h : Ordered (m+gs.length) hs) : Ordered m (gs++hs) := by
  intro i
  by_cases early : i.val<gs.length
  · simpa [List.get_eq_getElem,early] using g ⟨i.val,early⟩
  · have lt : i.val-gs.length<hs.length := by have := i.isLt; simp only [List.length_append] at this; omega
    have eq : m+gs.length+(i.val-gs.length)=m+i.val := by omega
    simpa [List.get_eq_getElem,List.getElem_append_right (Nat.le_of_not_gt early),eq] using h ⟨i.val-gs.length,lt⟩

theorem ordered_joins (n a : ℕ) (xs : List ℕ) (acc : a<n) (sibs : ∀ x∈xs,x<n) :
    Ordered n (appendJoins n a xs) := by
  induction xs generalizing n a with
  | nil =>
    intro i
    exact Fin.elim0 i
  | cons x xs ih =>
    let g : Gate := ⟨.join,a,x⟩
    have one : Ordered n [g] := by
      intro i
      have z : i.val=0 := by have hi : i.val<1 := i.isLt; omega
      simpa [List.get_eq_getElem,g,z] using And.intro acc (sibs x (by simp))
    exact ordered_append one (ih (n+1) n (by omega) (fun x hx => by
      have := sibs x (List.mem_cons_of_mem _ hx); omega))

def finalOutput (m s out : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool) :=
  let p := buildPrefix m code sel s
  if p.siblings.isEmpty then p.ref out else m+s-1

open SparseIncidence IncidenceStartNormalization

/-- Produces actual binary-length physical code, with inputs retained at the
original labels and all supplements appended after the ordinary gates. -/
def circuit {n : ℕ} (C : Circuit n) (sel : ℕ → Option Bool) : Circuit n := by
  let m := n+n
  let p := buildPrefix m C.code sel C.size
  let gates := codeList m C.size C.output C.code sel
  let code : ℕ → Gate := fun j => gates.getD j ⟨.zero,0,0⟩
  let start : ℕ → Option Bool := fun _ => none
  have len : gates.length=C.size := physical_size .. 
  obtain ⟨ord,refs,sibs⟩ := well_prefix m C.code sel C.size C.earlier
  have ordered : Ordered m gates := ordered_append ord (ordered_joins _ _ _ (refs _ C.output_lt) sibs)
  have earlier (j : ℕ) (hj : j<C.size) : (code j).left<m+j ∧ (code j).right<m+j := by
    have h : j<gates.length := len ▸ hj
    simpa [code,List.getD_eq_getElem?_getD,h] using ordered ⟨j,h⟩
  refine ⟨C.size,finalOutput m C.size C.output C.code sel,code,value C.wire code start m C.size,?_,earlier,?_,?_⟩
  · change (if (buildPrefix m C.code sel C.size).siblings.isEmpty then (buildPrefix m C.code sel C.size).ref C.output else m+C.size-1) < m+C.size
    split
    · have := refs _ C.output_lt
      have := prefix_length m C.code sel C.size
      omega
    · have := C.output_lt
      dsimp [m] at *
      omega
  · intro j hj
    exact law C.wire code start m C.size j hj (earlier j hj)
  · intro i
    have l := stable C.wire code start m 0 C.size i.val (by dsimp [m]; omega)
    have r := stable C.wire code start m 0 C.size (n+i.val) (by dsimp [m]; omega)
    simpa only [Nat.zero_add] using And.intro (l.trans (C.inputs i).1) (r.trans (C.inputs i).2)

#print axioms physical_size
#print axioms well_prefix
#print axioms circuit
end IncidenceHoistCompile
