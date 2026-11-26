import Research.TrueOrCount

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- If two evaluations have no jointly firing OR, every jointly true wire
was already forced by a jointly true input. This holds for every intermediate
wire and permits nullary gates, dangling reads, and non-strict fan-in. -/
theorem wires_no_shared_or (gs : List Gate) (z x y : List Bool)
    (lx : x.length = z.length) (ly : y.length = z.length)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (raw : ∀ i, x.getD i false = true → y.getD i false = true → z.getD i false = true)
    (sep : ∀ i, (trueOrFlags gs x).getD i false = true →
      (trueOrFlags gs y).getD i false = true → False) :
    ∀ i, ((Circuit.mk gs 0).wires x).getD i false = true →
      ((Circuit.mk gs 0).wires y).getD i false = true →
      ((Circuit.mk gs 0).wires z).getD i false = true := by
  induction gs generalizing z x y with
  | nil => exact raw
  | cons g gs ih =>
    apply ih (advance g z) (advance g x) (advance g y)
      (by simp [advance_len,lx]) (by simp [advance_len,ly])
      (fun g' hg => mono g' (List.mem_cons_of_mem _ hg)) _ (fun i => sep (i+1))
    intro i
    by_cases hi : i < z.length
    · simpa only [getD_advance_lt g z i hi, getD_advance_lt g x i (by omega),
        getD_advance_lt g y i (by omega)] using raw i
    · by_cases he : i = z.length
      · subst i
        have ex := getD_advance_eq g x
        have ey := getD_advance_eq g y
        rw [lx] at ex
        rw [ly] at ey
        rw [ex,ey,getD_advance_eq]
        rcases mono g (List.mem_cons_self ..) with ha|ho
        · simp only [ha,GateOp.eval,List.all_map,List.all_eq_true]
          exact fun hx hy a mem => raw a (hx a mem) (hy a mem)
        · intro hx hy
          have first := sep 0
          change (isOrGate g && _) = true → (isOrGate g && _) = true → False at first
          have hor : isOrGate g = true := by simp [isOrGate,ho]
          simp only [hor,Bool.true_and] at first
          exact (first hx hy).elim
      · rw [getD_missing (by rw [advance_len,lx]; omega : (advance g x).length ≤ i)]
        simp

def nestSingleton {n : Nat} (i : Fin n) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j=i))

private theorem separate_singletons {n : Nat} (a b : Fin n) (ne : a ≠ b) :
    ∀ i, (nestSingleton a).getD i false = true →
      (nestSingleton b).getD i false = true → (List.replicate n false).getD i false = true := by
  intro i hx hy
  by_cases hi : i < n
  · simp [nestSingleton,List.getD_eq_getElem?_getD,hi] at hx hy
    exact (ne (hx.symm.trans hy)).elim
  · simp [nestSingleton,List.getD_eq_getElem?_getD,hi] at hx

/-- No singleton outside a clean nested pair can be true on a zero-false
wire carrying the early singleton when their chronological OR traces are disjoint. -/
theorem clean_pair_excludes_wires {n : Nat} (C : Circuit) (hm : Monotone2 C)
    (a b : Fin n) (ne : a ≠ b)
    (disjoint : ∀ i, (trueOrFlags C.gates (nestSingleton a)).getD i false = true →
      (trueOrFlags C.gates (nestSingleton b)).getD i false = true → False)
    (i : Nat) (off : (C.wires (List.replicate n false)).getD i false = false)
    (live : (C.wires (nestSingleton a)).getD i false = true) :
    (C.wires (nestSingleton b)).getD i false = false := by
  cases C with
  | mk gs o =>
    by_contra! h
    have hb : ((Circuit.mk gs o).wires (nestSingleton b)).getD i false = true := by simpa using h
    have result := wires_no_shared_or gs (List.replicate n false) (nestSingleton a) (nestSingleton b)
      (by simp [nestSingleton]) (by simp [nestSingleton]) (fun g hg => (hm g hg).1)
      (separate_singletons a b ne) disjoint i live hb
    exact Bool.noConfusion (off.symm.trans result)

end PEqualNP.Research.MissingCell
