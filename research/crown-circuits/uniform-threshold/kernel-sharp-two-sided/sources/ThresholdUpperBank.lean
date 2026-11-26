import ThresholdThreeLayerUpper
namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds

@[simp] theorem id_pure_upper {α : Type} (x : α) : (pure x : Id α) = x := rfl

@[simp] theorem emit_run (n a b : Nat) (op : GateOp) (gs : List Gate) :
    (emit n op a b).run gs = (some (n+gs.length),gs++[⟨op,[a,b]⟩]) := rfl

def value (xs : List Bool) : Bit → Bool
  | none => false
  | some i => xs.getD i false
def fits (k : Nat) : Bit → Prop
  | none => True
  | some i => i < k
def advance (xs : List Bool) (gs : List Gate) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

theorem advance_append (xs : List Bool) (a b : List Gate) :
    advance xs (a++b) = advance (advance xs a) b := by simp [advance,List.foldl_append]

theorem advance_size (xs : List Bool) (gs : List Gate) :
    (advance xs gs).length = xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [advance]
  | cons g gs ih =>
    change (advance (xs++[_]) gs).length=_
    rw [ih]; simp; omega

theorem value_append (xs more : List Bool) (x : Bit) (h : fits xs.length x) :
    value (xs++more) x = value xs x := by
  cases x with
  | none => rfl
  | some i =>
    change i<xs.length at h
    simp [value,List.getD_eq_getElem?_getD,List.getElem?_append,h]

structure Result (n : Nat) (start : List Gate) (xs : List Bool) (res : Bit × List Gate)
    (truth : Bool) (budget : Nat) : Prop where
  suffix : ∃ add, res.2=start++add ∧ add.length≤budget ∧
    (∀ g∈add, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∧
    fits (n+res.2.length) res.1 ∧ value (advance xs add) res.1=truth

theorem one_or (n) (gs : List Gate) (xs : List Bool) (count : xs.length=n+gs.length)
    (a b : Bit) (ha : fits xs.length a) (hb : fits xs.length b) :
    Result n gs xs ((disj n a b).run gs) (value xs a || value xs b)
      (if a.isSome && b.isSome then 1 else 0) := by
  constructor
  cases a with
  | none =>
    refine ⟨[],?_,?_,?_,?_,?_⟩ <;> simp_all [disj,value,advance]
  | some i =>
    cases b with
    | none =>
      refine ⟨[],?_,?_,?_,?_,?_⟩ <;> simp_all [disj,value,advance]
    | some j =>
      refine ⟨[⟨.or,[i,j]⟩],rfl,by simp,by simp,?_,?_⟩
      · change n+gs.length<n+(gs++[_]).length
        simp
      · change (xs++[_]).getD (n+gs.length) false=_
        rw [←count]
        simp [List.getD_eq_getElem?_getD,List.getElem?_append,GateOp.eval,value]

theorem one_and (n) (gs : List Gate) (xs : List Bool) (count : xs.length=n+gs.length)
    (a b : Bit) (_ha : fits xs.length a) (_hb : fits xs.length b) :
    Result n gs xs ((conj n a b).run gs) (value xs a && value xs b)
      (if a.isSome && b.isSome then 1 else 0) := by
  constructor
  cases a with
  | none =>
    cases b <;> refine ⟨[],?_,?_,?_,?_,?_⟩ <;> simp [conj,value,fits,advance]
  | some i =>
    cases b with
    | none =>
      refine ⟨[],?_,?_,?_,?_,?_⟩ <;> simp [conj,value,fits,advance]
    | some j =>
      refine ⟨[⟨.and,[i,j]⟩],rfl,by simp,by simp,?_,?_⟩
      · change n+gs.length<n+(gs++[_]).length
        simp
      · change (xs++[_]).getD (n+gs.length) false=_
        rw [←count]
        simp [List.getD_eq_getElem?_getD,List.getElem?_append,GateOp.eval,value]

/-- The exact physical cost for one OR fiber counts only live operands. -/
def paid (a : Bit) (xs : List Bit) := ((a::xs).filterMap id).length-1

theorem paid_step (a b : Bit) (xs : List Bit) (n : Nat) (gs : List Gate) :
    (if a.isSome && b.isSome then 1 else 0) +
      paid (((disj n a b).run gs).1) xs = paid a (b::xs) := by
  cases a <;> cases b <;> simp [paid,disj] <;> omega

theorem fiber_count (n : Nat) (gs : List Gate) (a : Bit) (xs : List Bit) :
    ((xs.foldlM (disj n) a).run gs).2.length = gs.length + paid a xs := by
  induction xs generalizing gs a with
  | nil => cases a <;> simp [paid]
  | cons b xs ih =>
    have nextBound := ih (((disj n a b).run gs).2) (((disj n a b).run gs).1)
    have step := paid_step a b xs n gs
    have unitCost : ((disj n a b).run gs).2.length =
        gs.length + (if a.isSome && b.isSome then 1 else 0) := by
      cases a <;> cases b <;> simp [disj]
    change ((xs.foldlM (disj n) ((disj n a b).run gs).1).run ((disj n a b).run gs).2).2.length=_
    rw [nextBound,unitCost,Nat.add_assoc,step]

end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds

theorem advance_extends (xs : List Bool) (gs : List Gate) :
    ∃ more, advance xs gs = xs++more := by
  induction gs generalizing xs with
  | nil => exact ⟨[],by simp [advance]⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => xs.getD i false)
    obtain ⟨more,eq⟩ := ih (xs++[v])
    exact ⟨v::more,by change advance (xs++[v]) gs = _; simpa using eq⟩

theorem fiber_sem (n : Nat) (gs : List Gate) (xs : List Bool) (a : Bit) (bs : List Bit)
    (count : xs.length=n+gs.length) (fit : fits xs.length a)
    (inputs : ∀ b∈bs, fits xs.length b) :
    Result n gs xs ((bs.foldlM (disj n) a).run gs)
      (value xs a || bs.any (value xs)) (paid a bs) := by
  induction bs generalizing gs xs a with
  | nil =>
    refine ⟨⟨[],?_,by simp,by simp,?_,?_⟩⟩
    · simp
    · simpa [count] using fit
    · simp [advance]
  | cons b bs ih =>
    let q := (disj n a b).run gs
    obtain ⟨add,ga,ca,shape,fa,va⟩ := (one_or n gs xs count a b fit (inputs b (by simp))).suffix
    change q.2=gs++add at ga
    let ys := advance xs add
    have cy : ys.length=n+q.2.length := by simp [ys,advance_size,ga,count]; omega
    obtain ⟨more,eq⟩ := advance_extends xs add
    have remain (t) (ht : t∈bs) : fits ys.length t := by
      have old := inputs t (List.mem_cons_of_mem _ ht)
      cases t with
      | none => trivial
      | some i =>
        change i<xs.length at old
        change i<(advance xs add).length
        rw [advance_size]; omega
    have stable (t) (ht : t∈bs) : value ys t=value xs t := by
      change value (advance xs add) t=_
      rw [eq]
      exact value_append xs more t (inputs _ (List.mem_cons_of_mem _ ht))
    have anyeq : bs.any (value ys)=bs.any (value xs) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      exact ⟨fun ⟨t,ht,e⟩ => ⟨t,ht,(stable t ht) ▸ e⟩,
        fun ⟨t,ht,e⟩ => ⟨t,ht,(stable t ht).symm ▸ e⟩⟩
    obtain ⟨tail,gt,ct,st,ft,vt⟩ := (ih q.2 ys q.1 cy (cy.symm ▸ fa) remain).suffix
    constructor
    refine ⟨add++tail,?_,?_,?_,ft,?_⟩
    · change ((bs.foldlM (disj n) q.1).run q.2).2=_
      rw [gt,ga,List.append_assoc]
    · have step := paid_step a b bs n gs
      change _ + paid q.1 bs = _ at step
      rw [List.length_append]; omega
    · intro g hg
      exact (List.mem_append.mp hg).elim (shape g) (st g)
    · rw [advance_append]
      change value (advance ys tail) ((bs.foldlM (disj n) q.1).run q.2).1 = _
      rw [vt,anyeq]
      change value ys q.1 = _ at va
      rw [va]
      simp [Bool.or_assoc]
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
private theorem map_budget {α β : Type} (f : α → Build β) (xs : List α)
    (charge : α → Nat) (bound : ∀ a g, ((f a).run g).2.length ≤ g.length+charge a)
    (gs : List Gate) :
    ((xs.mapM f).run gs).2.length ≤ gs.length+(xs.map charge).sum := by
  induction xs generalizing gs with
  | nil => simp
  | cons a xs ih =>
    have nextBound := ih (((f a).run gs).2)
    have h := bound a gs
    rw [List.mapM_cons]
    change ((xs.mapM f).run ((f a).run gs).2).2.length ≤ _
    simp only [List.map_cons,List.sum_cons]
    omega

private theorem or_budget (n : Nat) (a b : Bit) (gs : List Gate) :
    ((disj n a b).run gs).2.length ≤ gs.length+1 := by
  cases a <;> cases b <;> simp [disj]

private theorem and_budget (n : Nat) (a b : Bit) (gs : List Gate) :
    ((conj n a b).run gs).2.length ≤ gs.length+1 := by
  cases a <;> cases b <;> simp [conj]

theorem prefix_budget (n : Nat) (old : List Bit) (x : Bit) (gs : List Gate) :
    ((prefixStep n old x).run gs).2.length ≤ gs.length+17 := by
  unfold prefixStep
  apply map_budget (charge := fun j => if j=0 then 1 else 2)
  intro j g
  by_cases e : j=0
  · subst j
    simpa using or_budget n (old.getD 0 none) x g
  · let q := (conj n x (old.getD (j-1) none)).run g
    have hc := and_budget n x (old.getD (j-1) none) g
    have hd := or_budget n (old.getD j none) q.1 q.2
    simp only [if_neg e]
    change ((disj n (old.getD j none) q.1).run q.2).2.length ≤ g.length+2
    change q.2.length≤g.length+1 at hc
    omega

theorem module_budget (n : Nat) (ports : List Bit) (old : List Bit) (gs : List Gate) :
    ((ports.foldlM (prefixStep n) old).run gs).2.length ≤ gs.length+17*ports.length := by
  induction ports generalizing old gs with
  | nil => simp
  | cons p ports ih =>
    let q := (prefixStep n old p).run gs
    have h := prefix_budget n old p gs
    change q.2.length ≤ _ at h
    have nextBound := ih q.1 q.2
    change ((ports.foldlM (prefixStep n) q.1).run q.2).2.length ≤ _
    simp only [List.length_cons]; omega
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
private theorem map_exact {α β : Type} (f : α → Build β) (xs : List α)
    (charge : α → Nat) (exactCost : ∀ a g, ((f a).run g).2.length = g.length+charge a)
    (gs : List Gate) :
    ((xs.mapM f).run gs).2.length = gs.length+(xs.map charge).sum := by
  induction xs generalizing gs with
  | nil => simp
  | cons a xs ih =>
    rw [List.mapM_cons]
    change ((xs.mapM f).run ((f a).run gs).2).2.length = _
    rw [ih,exactCost,List.map_cons,List.sum_cons,Nat.add_assoc]

def operands {p q : Nat} (adj : Fin p → Finset (Fin q)) (src : List Bit) (j : Fin q) :=
  (((List.finRange p).filter (fun i => decide (j∈adj i))).map (fun i => src.getD i.val none))

theorem layer_count {p q : Nat} (n : Nat) (adj : Fin p → Finset (Fin q)) (src : List Bit)
    (gs : List Gate) :
    ((layer n adj src).run gs).2.length =
      gs.length+((List.finRange q).map (fun j => paid none (operands adj src j))).sum := by
  unfold layer
  apply map_exact
  intro j g
  exact fiber_count n g none (operands adj src j)

theorem live_paid (bs : List Bit) (allLive : ∀ b∈bs,b.isSome=true) :
    paid none bs = bs.length-1 := by
  have eq : (bs.filterMap id).length=bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      cases b with
      | none => simpa using allLive none (by simp)
      | some i =>
        have hh := ih (fun b hb => allLive b (List.mem_cons_of_mem _ hb))
        exact congrArg Nat.succ hh
  simpa [paid] using congrArg (fun t : Nat => t-1) eq
end ThresholdThreeLayerUpper
