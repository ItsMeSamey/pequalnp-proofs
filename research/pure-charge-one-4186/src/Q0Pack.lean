import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

structure Pack (n : ℕ) where
  gates : List Gate
  allowed : ∀ g ∈ gates, g.op = .and ∨ g.op = .or
  arity : ∀ g ∈ gates, g.inputs.length = 2
  earlier : ∀ (i : Fin gates.length) w, w ∈ (gates.get i).inputs → w < n + i.val

namespace Pack

variable {n : ℕ}

abbrev Wire (p : Pack n) := Fin (n + p.gates.length)

def empty (n : ℕ) : Pack n where
  gates := []
  allowed := by simp
  arity := by simp
  earlier := by intro i; exact Fin.elim0 i

@[simp] theorem length_empty (n : ℕ) : (empty n).gates.length = 0 := rfl

def finish (p : Pack n) (w : p.Wire) : Circuit := ⟨p.gates, w.val⟩

theorem finish_ao2 (p : Pack n) (w : p.Wire) : IsAO2 n (p.finish w) := by
  refine ⟨p.allowed, ?_, p.arity⟩
  intro j hj v hv
  apply p.earlier ⟨j,hj⟩ v
  simpa only [gateAt, finish, List.getD_eq_get _ _ (⟨j,hj⟩ : Fin p.gates.length)] using hv

@[simp] theorem finish_size (p : Pack n) (w : p.Wire) : (p.finish w).size = p.gates.length := rfl

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

def val (p : Pack n) (w : p.Wire) (x : Fin n → Bool) : Bool :=
  (run p.gates (List.ofFn x)).getD w.val false

theorem finish_fun (p : Pack n) (w : p.Wire) (x : Fin n → Bool) :
    circuitFun n (p.finish w) x = p.val w x := rfl

def input (p : Pack n) (i : Fin n) : p.Wire := ⟨i.val, by have := i.isLt; omega⟩

private theorem run_keeps (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (run gs xs).getD i false = xs.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega), ih]

@[simp] theorem val_input (p : Pack n) (i : Fin n) (x : Fin n → Bool) :
    p.val (p.input i) x = x i := by
  change (run p.gates (List.ofFn x)).getD i.val false = _
  rw [run_keeps _ _ _ (by simpa using i.isLt)]
  simp

private def binary (isAnd : Bool) (a b : ℕ) : Gate :=
  ⟨if isAnd then .and else .or, [a,b]⟩

def emit (p : Pack n) (isAnd : Bool) (a b : p.Wire) : Pack n where
  gates := p.gates ++ [binary isAnd a b]
  allowed := by
    intro g hg
    rcases List.mem_append.mp hg with old | last
    · exact p.allowed g old
    · obtain rfl := List.mem_singleton.mp last
      cases isAnd <;> simp [binary]
  arity := by
    intro g hg
    rcases List.mem_append.mp hg with old | last
    · exact p.arity g old
    · obtain rfl := List.mem_singleton.mp last
      rfl
  earlier := by
    intro i w hw
    have hi := i.isLt
    by_cases old : i.val < p.gates.length
    · apply p.earlier ⟨i.val, old⟩ w
      simpa only [List.get_eq_getElem, List.getElem_append_left old] using hw
    · have eq : i.val = p.gates.length := by simp at hi; omega
      have hw' : w = a.val ∨ w = b.val := by
        have lastGate : (p.gates ++ [binary isAnd a b]).get i = binary isAnd a b := by
          calc
            _ = (p.gates ++ [binary isAnd a b]).getD i.val (binary isAnd a b) :=
              (List.getD_eq_get _ _ i).symm
            _ = (p.gates ++ [binary isAnd a b]).getD p.gates.length (binary isAnd a b) :=
              congrArg (fun j => (p.gates ++ [binary isAnd a b]).getD j (binary isAnd a b)) eq
            _ = _ := by simp
        rw [lastGate] at hw
        simpa [binary] using hw
      rw [eq]
      rcases hw' with rfl | rfl
      · exact a.isLt
      · exact b.isLt

@[simp] theorem length_emit (p : Pack n) (isAnd : Bool) (a b : p.Wire) :
    (p.emit isAnd a b).gates.length = p.gates.length + 1 := by simp [emit]

def lift (p : Pack n) (isAnd : Bool) (a b w : p.Wire) : (p.emit isAnd a b).Wire :=
  ⟨w.val, by rw [length_emit]; have := w.isLt; omega⟩

def last (p : Pack n) (isAnd : Bool) (a b : p.Wire) : (p.emit isAnd a b).Wire :=
  ⟨n + p.gates.length, by rw [length_emit]; omega⟩

@[simp] theorem val_lift (p : Pack n) (isAnd : Bool) (a b w : p.Wire) (x : Fin n → Bool) :
    (p.emit isAnd a b).val (p.lift isAnd a b w) x = p.val w x := by
  change (run (p.gates ++ [binary isAnd a b]) (List.ofFn x)).getD w.val false = _
  rw [run_snoc, List.getD_append _ _ _ _ (by simpa only [run_length, List.length_ofFn] using w.isLt)] <;> rfl

@[simp] theorem val_last (p : Pack n) (isAnd : Bool) (a b : p.Wire) (x : Fin n → Bool) :
    (p.emit isAnd a b).val (p.last isAnd a b) x =
      (if isAnd then p.val a x && p.val b x else p.val a x || p.val b x) := by
  change (run (p.gates ++ [binary isAnd a b]) (List.ofFn x)).getD (n + p.gates.length) false = _
  rw [run_snoc]
  have len : (run p.gates (List.ofFn x)).length = n + p.gates.length := by simp [run_length]
  have getLast (v : Bool) :
      (run p.gates (List.ofFn x) ++ [v]).getD (n + p.gates.length) false = v := by
    calc
      _ = (run p.gates (List.ofFn x) ++ [v]).getD (run p.gates (List.ofFn x)).length false :=
        congrArg (fun j => (run p.gates (List.ofFn x) ++ [v]).getD j false) len.symm
      _ = _ := by simp
  rw [getLast]
  cases isAnd <;> simp [binary, GateOp.eval, val]

end Pack
end PEqualNP.Outside.L_meta_4186_aux.Q0
