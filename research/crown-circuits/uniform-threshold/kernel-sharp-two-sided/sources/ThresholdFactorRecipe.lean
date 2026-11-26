import ThresholdFactorExpr
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open ThresholdUniqueRaw ThresholdFactorExpr
namespace ThresholdFactorRecipe

/-- Empty residual disjunction is represented at construction time. No
constant gate is charged or emitted. -/
def disj : List Term → Option Term
  | [] => none
  | a::as => some (match disj as with | none => a | some b => .node .or a b)

def residual (x : Nat) (t : Tree) :=
  ((t.raws.erase x).map Term.raw) ++ t.exts.map Term.ref

def factored (x : Nat) (a b : Tree) : Term :=
  match disj (residual x a),disj (residual x b) with
  | some p,some q => .node .or (.raw x) (.node .and p q)
  | _,_ => .raw x

def valOpt (R S : Nat → Bool) : Option Term → Bool
  | none => false
  | some t => t.value R S

theorem disj_sem (R S : Nat → Bool) (xs : List Term) :
    valOpt R S (disj xs)=xs.any (Term.value R S) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases eq : disj as with
    | none => simp only [disj,eq,valOpt,List.any_cons] at ih ⊢; rw [←ih,Bool.or_false]
    | some b => simp only [disj,eq,valOpt,List.any_cons,Term.value,act] at ih ⊢; rw [ih]

theorem disj_cost (xs : List Term) :
    match disj xs with
    | none => xs=[]
    | some t => t.cost+1=(xs.map Term.cost).sum+xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases e : disj as with
    | none =>
      simp only [e] at ih
      subst as; simp [disj,Term.cost]
    | some b =>
      simp only [e] at ih
      simp [disj,e,Term.cost,List.map_cons,List.sum_cons] <;> omega

private theorem erase_or (xs : List Nat) (x : Nat) (R : Nat → Bool) (hit : x∈xs) :
    (R x || (xs.erase x).any R)=xs.any R := by
  induction xs with
  | nil => simp at hit
  | cons a as ih =>
    by_cases same : a=x
    · subst a; simp
    · have tail : x∈as := (List.mem_cons.mp hit).resolve_left (Ne.symm same)
      rw [List.erase_cons_tail (by simpa using same : ¬(a == x)),List.any_cons,List.any_cons,←ih tail]
      exact Bool.or_left_comm _ _ _

private theorem residual_sem (x : Nat) (t : Tree) (R S : Nat → Bool) (hit : x∈t.raws) :
    (R x || valOpt R S (disj (residual x t))) = (t.raws.any R || t.exts.any S) := by
  rw [disj_sem]
  simp only [residual,List.any_append,List.any_map,Function.comp_def,Term.value]
  rw [←Bool.or_assoc,erase_or _ _ _ hit]

theorem factor_sem (x : Nat) (a b : Tree) (R S : Nat → Bool) (ha : x∈a.raws) (hb : x∈b.raws) :
    (factored x a b).value R S =
      ((a.raws.any R || a.exts.any S) && (b.raws.any R || b.exts.any S)) := by
  rw [←residual_sem x a R S ha,←residual_sem x b R S hb]
  cases ea : disj (residual x a) <;> cases eb : disj (residual x b) <;>
    cases rx : R x <;> simp [factored,ea,eb,valOpt,Term.value,act,rx]

private theorem residual_size (x : Nat) (t : Tree) (hit : x∈t.raws) :
    (residual x t).length=t.gates.length := by
  have eq := t.slots
  have pos := List.length_pos_of_mem hit
  simp [residual,List.length_erase_of_mem hit]
  omega

private theorem leafcost (xs : List Nat) (f : Nat → Term) (z : ∀ i,(f i).cost=0) :
    ((xs.map f).map Term.cost).sum=0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons,List.sum_cons,z,zero_add,ih]

theorem factor_cost (x : Nat) (a b : Tree) (ha : x∈a.raws) (hb : x∈b.raws) :
    (factored x a b).cost ≤ a.gates.length+b.gates.length := by
  have sz (t : Tree) (hx : x∈t.raws) := residual_size x t hx
  have zero (t : Tree) : ((residual x t).map Term.cost).sum=0 := by
    unfold residual
    rw [List.map_append,List.sum_append,leafcost _ _ (fun _ => rfl),leafcost _ _ (fun _ => rfl)]
  have ca := disj_cost (residual x a)
  have cb := disj_cost (residual x b)
  rw [zero,sz a ha,zero_add] at ca
  rw [zero,sz b hb,zero_add] at cb
  cases ea : disj (residual x a) <;> cases eb : disj (residual x b) <;>
    simp [factored,ea,eb,Term.cost] at * <;> omega
end ThresholdFactorRecipe
