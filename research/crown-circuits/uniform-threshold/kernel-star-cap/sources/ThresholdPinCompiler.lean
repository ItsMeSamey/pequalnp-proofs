import ThresholdEssentialOr
import T2BenchmarkNormalize
import Batteries.Tactic.OpenPrivate

namespace ThresholdPinCompiler
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ResidualSurplus ThresholdEssentialOr
open T2BenchmarkNormalize
open private inputs_shape inputs_sem oldWire get_push_ne widen from T2BenchmarkNormalize
open private run_app run_len from T2SoleOrEval

def basis (gs : List Gate) := ∀ g∈gs,
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length≤2

private theorem basis_layout {k : Nat} {gs : List Gate} (h : T2SoleOrSplice.SuffixOK k gs) :
    basis gs := by
  intro g hg
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
  obtain ⟨o,l,r,hgate,_,_⟩ := (T2SoleOrSplice.ok_indices gs k).mp h ⟨j,hj⟩
  change gs[j] = binary o l r at hgate
  subst g; rw [hgate]; cases o <;> simp [binary,gateOp]

/-- Quantitative supplement to the verified lowerInputs. In particular the
    live/live equal-wire step can only improve the count. -/
private theorem row_or_bound (o : Op) (xs : List Nat) (f : Nat → Wire) (k : Nat) :
    ors (lowerInputs o xs f k).1 ≤ if o=.or then 1 else 0 := by
  cases xs with
  | nil => cases o <;> simp [lowerInputs,ors]
  | cons x xs =>
    cases xs with
    | nil => cases o <;> simp [lowerInputs,ors]
    | cons y ys =>
      by_cases eq : f x=f y
      · cases o <;> simp [lowerInputs,binaryStep,eq,ors]
      · cases a : f x <;> cases b : f y <;> cases o <;>
          simp_all [lowerInputs,binaryStep,lower,ors,ThresholdOrGroups.isOr,binary,gateOp] <;>
          split <;> simp [ors]

private theorem forced_row (o : Op) (xs : List Nat) (f : Nat → Wire) (k : Nat)
    (arity : xs.length≤2) (hit : ∃ i∈xs, f i=.const false) :
    (lowerInputs o xs f k).1=[] ∧ (o=.and → (lowerInputs o xs f k).2=.const false) := by
  cases xs with
  | nil => simp at hit
  | cons x tail =>
    cases tail with
    | nil =>
      obtain ⟨i,hi,off⟩ := hit
      have eq : i=x := by simpa using hi
      subst i; simp [lowerInputs,off]
    | cons y ys =>
      have emp : ys=[] := by cases ys <;> simp_all
      subst ys
      obtain ⟨i,hi,off⟩ := hit
      rcases (show i=x ∨ i=y from by simpa using hi) with rfl|rfl
      · cases w : f y with
        | const b => cases b <;> cases o <;> simp [lowerInputs,binaryStep,off,w,lower,act,neutral]
        | live a => cases o <;> simp [lowerInputs,binaryStep,off,w,lower,act,neutral]
      · cases w : f x with
        | const b => cases b <;> cases o <;> simp [lowerInputs,binaryStep,off,w,lower,act,neutral]
        | live a => cases o <;> simp [lowerInputs,binaryStep,off,w,lower,act,neutral]

structure State where
  gs : List Gate
  addr : Nat → Wire

def step (s : State) (m seen : Nat) (g : Gate) : State :=
  let p := match g.op with
    | .and => lowerInputs .and g.inputs s.addr (m+s.gs.length)
    | .or => lowerInputs .or g.inputs s.addr (m+s.gs.length)
    | _ => ([],.const false)
  ⟨s.gs++p.1,fun i => if i=seen then p.2 else s.addr i⟩

def compile (m : Nat) : List Gate → Nat → State → State
  | [],_,s => s
  | g::gs,seen,s => compile m gs (seen+1) (step s m seen g)

/-- Nonexistent old operands always map to a false constant. -/
def initial (m pin : Nat) : State :=
  ⟨[],fun i => if i<m ∧ i≠pin then .live i else .const false⟩

def finish (s : State) (m out : Nat) : Circuit :=
  match s.addr out with
  | .live j => ⟨s.gs,j⟩
  | .const false => ⟨s.gs,m+s.gs.length⟩
  | .const true => ⟨s.gs++[⟨.and,[]⟩],m+s.gs.length⟩

def restrictFalse (C : Circuit) (m pin : Nat) : Circuit :=
  finish (compile m C.gates m (initial m pin)) m C.output

def pinFalse (w : List Bool) (p : Nat) := w.set p false

def marker (ps : List Probe) (s : State) :=
  ∀ i, (ps.getD i zero).forced=true → s.addr i=.const false

private theorem marked_input {ps : List Probe} {s : State} (hm : marker ps s)
    {xs : List Nat} (hit : xs.any (fun i => (ps.getD i zero).forced)=true) :
    ∃ i∈xs, s.addr i=.const false := by
  obtain ⟨i,mem,yes⟩ := List.any_eq_true.mp hit
  exact ⟨i,mem,hm i yes⟩

private theorem price_step (m seen : Nat) (g : Gate) (s : State) (ps : List Probe)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hm : marker ps s) :
    ors (step s m seen g).gs + (charge g ps).toNat ≤ ors s.gs + (ThresholdOrGroups.isOr g).toNat := by
  rcases (show g.op=.and ∨ g.op=.or from by simpa using h.1) with a|o
  · have p := row_or_bound .and g.inputs s.addr (m+s.gs.length)
    simp [step,a,ors,List.countP_append,charge,ThresholdOrGroups.isOr] at *
    omega
  · by_cases hit : g.inputs.any (fun i => (ps.getD i zero).forced)=true
    · have skip := (forced_row .or _ _ (m+s.gs.length) h.2 (marked_input hm hit)).1
      simp only [List.getD_eq_getElem?_getD] at hit
      simp [step,o,skip,ors,List.countP_append,charge,hit,ThresholdOrGroups.isOr]
    · have p := row_or_bound .or g.inputs s.addr (m+s.gs.length)
      simp only [List.getD_eq_getElem?_getD] at hit
      simp [step,o,ors,List.countP_append,charge,hit,ThresholdOrGroups.isOr] at *
      omega

private theorem marker_step (m : Nat) (g : Gate) (s : State) (ps : List Probe)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hm : marker ps s) :
    marker (ps++[ThresholdEssentialOr.eval g ps]) (step s m ps.length g) := by
  intro i force
  by_cases eq : i=ps.length
  · subst i
    have last : (ps++[ThresholdEssentialOr.eval g ps]).getD ps.length zero = ThresholdEssentialOr.eval g ps := by simp [List.getD_eq_getElem?_getD]
    rw [last] at force
    rcases (show g.op=.and ∨ g.op=.or from by simpa using h.1) with a|o
    · have hit : g.inputs.any (fun i => (ps.getD i zero).forced)=true := by
        simpa [ThresholdEssentialOr.eval,a,List.any_map,Function.comp_def] using force
      simpa [step,a] using (forced_row .and _ _ (m+s.gs.length) h.2 (marked_input hm hit)).2 rfl
    · simp [ThresholdEssentialOr.eval,o] at force
  · have same : (ps++[ThresholdEssentialOr.eval g ps]).getD i zero=ps.getD i zero := by
      by_cases hi : i<ps.length
      · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
      · have far : (ps++[ThresholdEssentialOr.eval g ps]).length ≤ i := by simp; omega
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none far,List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    rw [same] at force
    simpa [step,eq] using hm i force

theorem price_scan (m : Nat) (gs : List Gate) (s : State) (ps : List Probe)
    (good : basis gs) (hm : marker ps s) :
    ors (compile m gs ps.length s).gs + (scan gs ps).1.toNat ≤ ors s.gs+ors gs := by
  induction gs generalizing s ps with
  | nil => simp [compile,ThresholdEssentialOr.scan,ors]
  | cons g gs ih =>
    let pp := ps++[ThresholdEssentialOr.eval g ps]
    let ss := step s m ps.length g
    have head := good g (by simp)
    have p := price_step m ps.length g s ps head hm
    have t := ih ss pp (fun j hj => good j (by simp [hj])) (marker_step m g s ps head hm)
    have b : (charge g ps || (scan gs pp).1).toNat ≤ (charge g ps).toNat+(scan gs pp).1.toNat := by
      cases charge g ps <;> cases (scan gs pp).1 <;> decide
    have len : pp.length=ps.length+1 := by simp [pp]
    rw [len] at t
    change ors (compile m gs (ps.length+1) ss).gs+(charge g ps || (scan gs pp).1).toNat ≤ _
    have count : ors (g::gs)=(ThresholdOrGroups.isOr g).toNat+ors gs := by
      cases e : ThresholdOrGroups.isOr g <;> simp [ors,List.countP_cons,e,Nat.add_comm]
    change ors ss.gs + _ ≤ _ at p
    rw [count]; omega

/-- Simulation holds for every address, including old forward references.
    A fixed input v is sufficient here; the theorem quantifies over all v. -/
structure Sim (m : Nat) (v old : List Bool) (s : State) : Prop where
  mono : basis s.gs
  fit : ∀ i, FitsWire (m+s.gs.length) (s.addr i)
  point : ∀ i, ResidualSurplus.read (run s.gs v) (s.addr i)=old.getD i false

private theorem advance_sim (m : Nat) (v old : List Bool) (s : State)
    (len : v.length=m) (h : Sim m v old s) (g : Gate) (o : Op)
    (kind : g.op=gateOp o) (arity : g.inputs.length≤2) :
    Sim m v (old++[val g old]) (step s m old.length g) := by
  let j := m+s.gs.length
  let q := lowerInputs o g.inputs s.addr j
  have defStep : step s m old.length g =
      ⟨s.gs++q.1,fun i => if i=old.length then q.2 else s.addr i⟩ := by
    cases o <;> simp [step,kind,gateOp,q,j]
  rw [defStep]
  obtain ⟨shape,_,bound⟩ := inputs_shape o g.inputs s.addr j h.fit
  have jlen : (run s.gs v).length=j := by simp [run_len,len,j]
  constructor
  · intro row hg
    exact (List.mem_append.mp hg).elim (h.mono row) (basis_layout shape row)
  · intro i; by_cases eq : i=old.length
    · simpa [eq,q,j,Nat.add_assoc] using bound
    · simpa [eq] using widen (w:=s.addr i) (h.fit i) (by simp : m+s.gs.length≤m+(s.gs++q.1).length)
  · intro i
    change ResidualSurplus.read (run (s.gs++q.1) v) (if i=old.length then q.2 else s.addr i)=_
    rw [run_app]
    by_cases eq : i=old.length
    · subst i; rw [if_pos rfl,getD_new]
      have e := inputs_sem o g.inputs s.addr (run s.gs v) arity
      rw [jlen] at e
      simpa only [q,val,kind,h.point] using e
    · rw [if_neg eq,get_push_ne _ _ _ eq,oldWire _ _ _ (by rw [jlen]; exact h.fit i)]
      exact h.point i

theorem sim_scan (m : Nat) (v old : List Bool) (s : State) (gs : List Gate)
    (len : v.length=m) (basisOld : basis gs) (h : Sim m v old s) :
    Sim m v (run gs old) (compile m gs old.length s) := by
  induction gs generalizing old s with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨kind,arity⟩ := basisOld g (by simp)
    obtain ⟨o,eq⟩ : ∃ o : Op, g.op=gateOp o := by
      rcases (show g.op=.and ∨ g.op=.or from by simpa using kind) with a|b
      · exact ⟨.and,a⟩
      · exact ⟨.or,b⟩
    have advanced := advance_sim m v old s len h g o eq arity
    have tail := ih (old++[val g old]) (step s m old.length g)
      (fun r hr => basisOld r (by simp [hr])) advanced
    simpa only [run,val,List.foldl_cons,compile,List.length_append,List.length_singleton] using tail

private theorem pin_read (v : List Bool) (p i : Nat) :
    (pinFalse v p).getD i false = if i=p then false else v.getD i false := by
  by_cases small : i<v.length
  · by_cases eq : i=p
    · subst i; simp [pinFalse,List.getD_eq_getElem?_getD,List.getElem?_set,small]
    · simp [pinFalse,List.getD_eq_getElem?_getD,List.getElem?_set,List.getElem_set,small,eq,Ne.symm eq]
  · have far : (pinFalse v p).length ≤ i := by simpa [pinFalse] using Nat.le_of_not_gt small
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none far,
      List.getElem?_eq_none (Nat.le_of_not_gt small),Option.getD_none,ite_self]

private theorem start_sim (v : List Bool) (m p : Nat) (len : v.length=m) :
    Sim m v (pinFalse v p) (initial m p) := by
  constructor
  · simp [initial,basis]
  · intro i; by_cases hi : i<m <;> by_cases eq : i=p <;> simp [initial,FitsWire,hi,eq]
  · intro i
    rw [pin_read]
    by_cases hi : i<m <;> by_cases eq : i=p <;>
      simp [initial,run,ResidualSurplus.read,hi,eq,List.getD_eq_getElem?_getD,len]

private theorem finish_correct (s : State) (m out : Nat) (v : List Bool) (len : v.length=m) :
    (finish s m out).eval v=ResidualSurplus.read (run s.gs v) (s.addr out) := by
  have sz := run_len s.gs v
  rw [len] at sz
  cases e : s.addr out with
  | live j => simp [finish,e,Circuit.eval,ResidualSurplus.read]; rfl
  | const b =>
    cases b with
    | false =>
      change (finish s m out).eval v = false
      simp only [finish,e,Circuit.eval]
      change (run s.gs v).getD (m+s.gs.length) false=false
      simp [List.getD_eq_getElem?_getD,←sz]
    | true =>
      simp only [finish,e,Circuit.eval]
      change (run (s.gs++[⟨.and,[]⟩]) v).getD (m+s.gs.length) false=true
      rw [run_app,←sz]
      change ((run s.gs v)++[true]).getD (run s.gs v).length false=true
      exact getD_new _ _

private theorem finish_count (s : State) (m out : Nat) : ors (finish s m out).gates=ors s.gs := by
  cases e : s.addr out with
  | live j => simp [finish,e]
  | const b => cases b <;> simp [finish,e,ors,List.countP_append,ThresholdOrGroups.isOr]

private theorem finish_mono (s : State) (m out : Nat) (mono : basis s.gs) :
    PEqualNP.MetaComplexity.Monotone2 (finish s m out) := by
  intro g hg
  cases e : s.addr out with
  | live j => exact mono g (by simpa [finish,e] using hg)
  | const b =>
    cases b with
    | false => exact mono g (by simpa [finish,e] using hg)
    | true =>
      have mem : g∈s.gs ∨ g=⟨.and,[]⟩ := by simpa [finish,e] using hg
      rcases mem with old|rfl
      · exact mono g old
      · simp

theorem restriction_correct (C : Circuit) (m p : Nat) (mono : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (restrictFalse C m p) ∧
      ∀ v : List Bool, v.length=m → (restrictFalse C m p).eval v=C.eval (pinFalse v p) := by
  have sim (v : List Bool) (len : v.length=m) :
      Sim m v (run C.gates (pinFalse v p)) (compile m C.gates m (initial m p)) := by
    simpa [pinFalse,len] using sim_scan m v (pinFalse v p) (initial m p) C.gates len mono (start_sim v m p len)
  refine ⟨finish_mono _ _ _ (sim (List.replicate m false) (by simp)).mono,?_⟩
  intro v len
  exact (finish_correct _ _ _ v len).trans ((sim v len).point C.output)

def probes {m : Nat} (p : Fin m) (lo hi z : Fin m → Bool) : List Probe :=
  List.ofFn (fun i => ⟨lo i,hi i,z i,decide (i=p)⟩)

private theorem probes_at {m : Nat} (p : Fin m) (lo hi z : Fin m → Bool) (i : Fin m) :
    (probes p lo hi z).getD i.val zero=⟨lo i,hi i,z i,decide (i=p)⟩ := by
  simp only [probes,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]

private theorem start_mark {m : Nat} (p : Fin m) (lo hi z : Fin m → Bool) :
    marker (probes p lo hi z) (initial m p.val) := by
  intro i h
  by_cases small : i<m
  · let j : Fin m := ⟨i,small⟩
    change ((probes p lo hi z).getD j.val zero).forced=true at h
    rw [probes_at] at h
    have jp : j=p := of_decide_eq_true h
    have eq : i=p.val := congrArg Fin.val jp
    simp [initial,eq]
  · have far : (probes p lo hi z).length ≤ i := by simpa [probes] using Nat.le_of_not_gt small
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none far,zero] at h

/-- No minimality, layout certificate, OR-only assumption, or live-gate
    hypothesis. OR costs count physical OR rows of the actual compiled D. -/
theorem essential_pin_false {m : Nat} (C : Circuit) (p : Fin m)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (lo hi z : Fin m → Bool) (same : ∀ i, i≠p → lo i=hi i)
    (changeOut : C.eval (List.ofFn lo)≠C.eval (List.ofFn hi))
    (staysOff : z p=false) (accepts : C.eval (List.ofFn z)=true) :
    let D := restrictFalse C m p.val
    PEqualNP.MetaComplexity.Monotone2 D ∧
    (∀ v : List Bool, v.length=m → D.eval v=C.eval (pinFalse v p.val)) ∧
    ors D.gates+1≤ors C.gates := by
  let ps := probes p lo hi z
  have plen : ps.length=m := by simp [ps,probes]
  have safe : ∀ a∈ps, Good a := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    by_cases eq : i=p
    · subst i; simp [ThresholdEssentialOr.Good,staysOff]
    · simp [ThresholdEssentialOr.Good,eq,same i eq]
  have changed : (scan C.gates ps).1=true := by
    apply physical_pin_charge C ps mono safe
    · simpa [ps,probes,List.map_ofFn,Function.comp_def] using changeOut
    · simpa [ps,probes,List.map_ofFn,Function.comp_def] using accepts
  have bound := price_scan m C.gates (initial m p.val) ps mono (start_mark p lo hi z)
  rw [plen,changed] at bound
  obtain ⟨preserve,meaning⟩ := restriction_correct C m p.val mono
  refine ⟨preserve,meaning,?_⟩
  change ors (finish _ _ _).gates+1≤_
  rw [finish_count]
  simpa [initial,ors] using bound

/-- Uncharged deletion for the other endpoint of a remote anchor. -/
theorem weak_pin_false {m : Nat} (C : Circuit) (p : Fin m)
    (mono : PEqualNP.MetaComplexity.Monotone2 C) :
    let D := restrictFalse C m p.val
    PEqualNP.MetaComplexity.Monotone2 D ∧
    (∀ v : List Bool, v.length=m → D.eval v=C.eval (pinFalse v p.val)) ∧
    ors D.gates≤ors C.gates := by
  let zeroRow := fun _ : Fin m => false
  let ps := probes p zeroRow zeroRow zeroRow
  have len : ps.length=m := by simp [ps,probes]
  have bound := price_scan m C.gates (initial m p.val) ps mono (start_mark p zeroRow zeroRow zeroRow)
  rw [len] at bound
  obtain ⟨preserve,meaning⟩ := restriction_correct C m p.val mono
  refine ⟨preserve,meaning,?_⟩
  change ors (finish _ _ _).gates≤_
  rw [finish_count]
  have nilPrice : ors (initial m p.val).gs=0 := rfl
  rw [nilPrice,Nat.zero_add] at bound
  omega

#print axioms restriction_correct
#print axioms essential_pin_false
#print axioms weak_pin_false
end ThresholdPinCompiler
