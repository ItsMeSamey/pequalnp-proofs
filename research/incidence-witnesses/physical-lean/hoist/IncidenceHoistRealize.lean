import IncidenceHoistCompile
namespace IncidenceHoistRealize
open CircuitRewire IncidenceStartNormalization IncidenceHoistCompile IncidenceHoistFlow
variable {Z : Type}

def Models (m : Nat) (W : Nat → Set Z) (gates : List Gate) :=
  ∀ (i : Nat) (hi : i < gates.length), W (m+i) = (gates[i]).eval W

def spill (W : Nat → Set Z) (xs : List Nat) : Set Z := {z | ∃ i ∈ xs, z ∈ W i}

private theorem front {m : Nat} {W : Nat → Set Z} (gs hs : List Gate)
    (h : Models m W (gs++hs)) : Models m W gs := by
  intro i hi
  have eq := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at eq

private theorem back {m : Nat} {W : Nat → Set Z} (gs hs : List Gate)
    (h : Models m W (gs++hs)) : Models (m+gs.length) W hs := by
  intro i hi
  have eq := h (gs.length+i) (by simpa using hi)
  simpa [List.getElem_append_right (show gs.length ≤ gs.length+i by omega),Nat.add_assoc] using eq

private theorem lost_next (t : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    (Y : Nat → Set Z) :
    lost (t+1) code sel Y = lost t code sel Y ∪
      (match sel t with | none => ∅ | some b => Y (other (code t) b)) := by
  ext z
  constructor
  · rintro ⟨j,hj,b,hb,h⟩
    by_cases he : j=t
    · subst j
      right
      simpa only [hb] using h
    · exact Or.inl ⟨j,by omega,b,hb,h⟩
  · rintro (⟨j,hj,b,hb,h⟩ | h)
    · exact ⟨j,by omega,b,hb,h⟩
    · cases hh : sel t with
      | none => simp [hh] at h
      | some b => exact ⟨t,by omega,b,hh,by simpa [hh] using h⟩

/-- Evaluate a compiled buildPrefix in any physical wire assignment satisfying
the retained gates. Y is a fixed bypassed assignment for the original labels. -/
theorem prefix_sem (m t : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    (W Y : Nat → Set Z) (raw : ∀ i<m,W i = Y i)
    (order : ∀ j<t,(code j).left<m+j ∧ (code j).right<m+j)
    (ylaw : ∀ j<t,Y (m+j) = match sel j with
      | none => (code j).eval Y | some b => Y (keep (code j) b))
    (run : Models m W (buildPrefix m code sel t).kept) :
    (∀ i<m+t, W ((buildPrefix m code sel t).ref i) = Y i) ∧
      spill W (buildPrefix m code sel t).siblings = lost t code sel Y := by
  induction t with
  | zero =>
    exact ⟨by simpa [buildPrefix] using raw,by ext z; simp [buildPrefix,spill,lost]⟩
  | succ t ih =>
    let p := buildPrefix m code sel t
    have ord := order t (by omega)
    have law := ylaw t (by omega)
    have prev (r : Models m W p.kept) := ih (fun j hj => order j (by omega))
      (fun j hj => ylaw j (by omega)) r
    cases e : sel t with
    | none =>
      have rr : Models m W (p.kept++[redirect p.ref (code t)]) := by simpa [buildPrefix,e,p] using run
      obtain ⟨ref,sp⟩ := prev (front _ _ rr)
      have last := (back _ _ rr) 0 (by simp)
      change W (m+p.kept.length+0) = (redirect p.ref (code t)).eval W at last
      simp only [Nat.add_zero,Gate.eval,redirect] at last
      rw [ref _ ord.1,ref _ ord.2] at last
      refine ⟨?_,?_⟩
      · intro i hi
        by_cases he : i=m+t
        · subst i
          simpa [buildPrefix,e,put,p] using last.trans (by simpa [e,Gate.eval] using law.symm)
        · simpa [buildPrefix,e,put,he] using ref i (by omega)
      · simpa only [buildPrefix,e,lost_next,Set.union_empty] using sp
    | some b =>
      have rr : Models m W p.kept := by simpa [buildPrefix,e,p] using run
      obtain ⟨ref,sp⟩ := prev rr
      have kept : keep (code t) b<m+t := by cases b <;> simp [keep,ord]
      have side : other (code t) b<m+t := by cases b <;> simp [other,ord]
      refine ⟨?_,?_⟩
      · intro i hi
        by_cases he : i=m+t
        · subst i
          simpa [buildPrefix,e,put] using (ref _ kept).trans (by simpa only [e] using law.symm)
        · simpa [buildPrefix,e,put,he] using ref i (by omega)
      · have append (xs : List Nat) (i : Nat) : spill W (xs++[i]) = spill W xs ∪ W i := by
          ext z
          simp [spill,List.mem_append]
        simp only [buildPrefix,e,lost_next,append,sp,ref _ side]

private def foldOut (n a : Nat) (xs : List Nat) := if xs.isEmpty then a else n+xs.length-1

private theorem join_sem (W : Nat → Set Z) (n a : Nat) (xs : List Nat)
    (run : Models n W (appendJoins n a xs)) :
    W (foldOut n a xs) = W a ∪ spill W xs := by
  induction xs generalizing n a with
  | nil => simp [foldOut,spill]
  | cons x xs ih =>
    let g : Gate := ⟨.join,a,x⟩
    have run' : Models n W ([g]++appendJoins (n+1) n xs) := run
    have first := (front _ _ run') 0 (by simp)
    change W (n+0) = W a ∪ W x at first
    rw [Nat.add_zero] at first
    have next := ih (n+1) n (back _ _ run')
    have idx : foldOut n a (x::xs) = foldOut (n+1) n xs := by
      cases xs <;> simp [foldOut] <;> omega
    rw [idx,next,first]
    ext z
    simp [spill]
    grind

/-- The physically emitted circuit computes the bypassed output plus all
rebuilt sibling occurrences. No semantic correctness is assumed of the edit. -/
theorem realize {n : Nat} (C : Circuit n) (sel : Nat → Option Bool) :
    let Y := value C.wire C.code sel (n+n) C.size
    (circuit C sel).wire (circuit C sel).output = Y C.output ∪ lost C.size C.code sel Y := by
  let m := n+n
  let Y := value C.wire C.code sel m C.size
  let D := circuit C sel
  let p := buildPrefix m C.code sel C.size
  let gs := codeList m C.size C.output C.code sel
  have len : gs.length=C.size := physical_size ..
  have run : Models m D.wire gs := by
    intro i hi
    have h := D.law i (by change i<C.size; omega)
    change D.wire (m+i) = (gs.getD i ⟨.zero,0,0⟩).eval D.wire at h
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using h
  have raw (i : Nat) (hi : i<m) : D.wire i = Y i := by
    change value C.wire D.code (fun _ => none) m C.size i = Y i
    have d0 := stable C.wire D.code (fun _ => none) m 0 C.size i (by omega)
    have y0 := stable C.wire C.code sel m 0 C.size i (by omega)
    simpa only [Nat.zero_add] using d0.trans y0.symm
  obtain ⟨ref,sp⟩ := prefix_sem m C.size C.code sel D.wire Y raw C.earlier
    (fun j hj => law C.wire C.code sel m C.size j hj (C.earlier j hj)) (front _ _ run)
  have result := join_sem D.wire (m+p.kept.length) (p.ref C.output) p.siblings (back _ _ run)
  have index : D.output = foldOut (m+p.kept.length) (p.ref C.output) p.siblings := by
    change (if p.siblings.isEmpty then p.ref C.output else m+C.size-1) = _
    unfold foldOut
    have eq : p.kept.length+p.siblings.length=C.size := prefix_length ..
    rw [show m+p.kept.length+p.siblings.length = m+C.size by omega]
  change D.wire D.output = Y C.output ∪ lost C.size C.code sel Y
  rw [index,result,ref _ C.output_lt,sp]

#print axioms realize
end IncidenceHoistRealize
