import ThresholdOrGroups

/- Source draft, deliberately outside the compiler queue.
   A signal records its values on two rows that differ in one pin, and on an
   accepting row where that pin is false. "forced" means that the single pin
   reaches the signal using only ANDs, including the length-zero path. -/
namespace ThresholdEssentialOr
open PEqualNP.CircuitLowerBounds ThresholdOrGroups

structure Probe where
  low : Bool
  high : Bool
  retained : Bool
  forced : Bool
deriving DecidableEq, Repr

def zero : Probe := ⟨false,false,false,false⟩

def Good (a : Probe) : Prop :=
  (a.forced=true → a.retained=false) ∧ (a.forced=false → a.low=a.high)

def eval (g : Gate) (ps : List Probe) : Probe :=
  let s := g.inputs.map (fun i => ps.getD i zero)
  ⟨g.op.eval (s.map Probe.low), g.op.eval (s.map Probe.high),
    g.op.eval (s.map Probe.retained),
    match g.op with | .and => s.any Probe.forced | _ => false⟩

def charge (g : Gate) (ps : List Probe) : Bool :=
  match g.op with
  | .or => g.inputs.any (fun i => (ps.getD i zero).forced)
  | _ => false

def admissible (g : Gate) := g.op = .and ∨ g.op = .or

private theorem all_eq {xs : List Probe} (safe : ∀ z∈xs, Good z)
    (quiet : xs.any Probe.forced = false) :
    xs.map Probe.low = xs.map Probe.high := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : a.forced=false := (show a.forced=false ∧ xs.any Probe.forced=false from by simpa using quiet).1
    have hs : xs.any Probe.forced=false := (show a.forced=false ∧ xs.any Probe.forced=false from by simpa using quiet).2
    simp only [List.map_cons]
    rw [(safe a (by simp)).2 ha, ih (fun z hz => safe z (by simp [hz])) hs]

/-- Any uncharged monotone gate preserves the three-row invariant. Works for
    nullary and unary gates, repeated ports, and arbitrary arity. -/
theorem local_good (g : Gate) (ps : List Probe)
    (safe : ∀ i, Good (ps.getD i zero)) (basis : admissible g)
    (quiet : charge g ps=false) : Good (eval g ps) := by
  let xs := g.inputs.map (fun i => ps.getD i zero)
  have good : ∀ z∈xs, Good z := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
    exact safe i
  obtain andg|org := basis
  · constructor
    · intro force
      have force' : xs.any Probe.forced=true := by simpa [eval,andg,xs] using force
      obtain ⟨z,hz,hf⟩ := List.any_eq_true.mp force'
      have off := (good z hz).1 hf
      change g.op.eval (xs.map Probe.retained)=false
      rw [andg]
      cases hv : GateOp.and.eval (xs.map Probe.retained) with
      | false => rfl
      | true =>
        have hall : ∀ a∈xs.map Probe.retained, a=true := by simpa [GateOp.eval] using hv
        have := hall _ (List.mem_map.mpr ⟨z,hz,rfl⟩)
        simp_all
    · intro noforce
      have nf : xs.any Probe.forced=false := by simpa [eval,andg,xs] using noforce
      change g.op.eval (xs.map Probe.low)=g.op.eval (xs.map Probe.high)
      rw [all_eq good nf]
  · have nf : xs.any Probe.forced=false := by simpa [charge,org,xs,List.any_map] using quiet
    constructor
    · simp [eval,org]
    · intro _
      change g.op.eval (xs.map Probe.low)=g.op.eval (xs.map Probe.high)
      rw [all_eq good nf]

def scan : List Gate → List Probe → Bool × List Probe
  | [],ps => (false,ps)
  | g::gs,ps =>
    let t := scan gs (ps++[eval g ps])
    (charge g ps || t.1,t.2)

theorem good_scan (gs : List Gate) (ps : List Probe)
    (basis : ∀ g∈gs, admissible g)
    (safe : ∀ p∈ps, Good p)
    (quiet : (scan gs ps).1=false) :
    ∀ p∈(scan gs ps).2, Good p := by
  induction gs generalizing ps with
  | nil => exact safe
  | cons g gs ih =>
    have bits : charge g ps=false ∧ (scan gs (ps++[eval g ps])).1=false := by simpa [scan] using quiet
    apply ih _ (fun h hh => basis h (by simp [hh])) _ bits.2
    intro p hp
    rcases List.mem_append.mp hp with old|last
    · exact safe p old
    · have eq : p=eval g ps := by simpa using last
      subst p
      apply local_good _ _ _ (basis g (by simp)) bits.1
      intro i
      by_cases h : i<ps.length
      · simpa [List.getD_eq_getElem?_getD,h] using safe ps[i] (List.getElem_mem _)
      · simp [List.getD_eq_getElem?_getD,h,Good,zero]

theorem essential_charge (gs : List Gate) (ps : List Probe) (out : Probe)
    (basis : ∀ g∈gs, admissible g) (safe : ∀ p∈ps, Good p)
    (mem : out∈(scan gs ps).2) (different : out.low≠out.high)
    (preserved : out.retained=true) : (scan gs ps).1=true := by
  cases e : (scan gs ps).1 with
  | true => rfl
  | false =>
    have h := good_scan gs ps basis safe e out mem
    cases f : out.forced with
    | false => exact False.elim (different (h.2 f))
    | true => have := h.1 f; simp_all

private theorem project_read (f : Probe → Bool) (z : f zero=false)
    (ps : List Probe) (i : Nat) :
    f (ps.getD i zero)=(ps.map f).getD i false := by
  by_cases h : i<ps.length <;> simp [List.getD_eq_getElem?_getD,List.getElem?_map,h,z]

private theorem projects (f : Probe → Bool) (z : f zero=false)
    (gate : ∀ g ps, f (eval g ps)=g.op.eval (g.inputs.map (fun i => f (ps.getD i zero))))
    (gs : List Gate) (ps : List Probe) :
    (scan gs ps).2.map f=ResidualSurplus.run gs (ps.map f) := by
  induction gs generalizing ps with
  | nil => rfl
  | cons g gs ih =>
    change (scan gs (ps++[eval g ps])).2.map f =
      ResidualSurplus.run gs (ps.map f ++ [ResidualSurplus.val g (ps.map f)])
    rw [ih,List.map_append,List.map_singleton,gate]
    simp only [ResidualSurplus.val, project_read f z]

theorem scan_semantics (C : Circuit) (ps : List Probe) :
    let out := (scan C.gates ps).2.getD C.output zero
    out.low=C.eval (ps.map Probe.low) ∧ out.high=C.eval (ps.map Probe.high) ∧
      out.retained=C.eval (ps.map Probe.retained) := by
  have part (f : Probe → Bool) (off : f zero=false)
      (gate : ∀ g ps, f (eval g ps)=g.op.eval (g.inputs.map (fun i => f (ps.getD i zero)))) :
      f ((scan C.gates ps).2.getD C.output zero)=C.eval (ps.map f) := by
    rw [project_read f off,projects f off gate]
    rfl
  exact ⟨part _ rfl (by intro g v; simp [eval,List.map_map,Function.comp_def]),
    part _ rfl (by intro g v; simp [eval,List.map_map,Function.comp_def]),
    part _ rfl (by intro g v; simp [eval,List.map_map,Function.comp_def])⟩

theorem physical_pin_charge (C : Circuit) (ps : List Probe)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (safe : ∀ p∈ps, Good p)
    (different : C.eval (ps.map Probe.low)≠C.eval (ps.map Probe.high))
    (retained : C.eval (ps.map Probe.retained)=true) :
    (scan C.gates ps).1=true := by
  have semantics := scan_semantics C ps
  let ws := (scan C.gates ps).2
  have hr : (ws.getD C.output zero).retained=true := semantics.2.2.trans retained
  have hi : C.output<ws.length := by
    by_contra h
    simp [List.getD_eq_getElem?_getD,h,zero] at hr
  have mem : ws.getD C.output zero ∈ ws := by
    simpa [List.getD_eq_getElem?_getD,hi] using List.getElem_mem (l:=ws) (i:=C.output) hi
  apply essential_charge C.gates ps _ _ safe mem _ hr
  · intro g hg
    simpa [admissible] using (mono g hg).1
  · exact fun eq => different (semantics.1.symm.trans (eq.trans semantics.2.1))

end ThresholdEssentialOr
