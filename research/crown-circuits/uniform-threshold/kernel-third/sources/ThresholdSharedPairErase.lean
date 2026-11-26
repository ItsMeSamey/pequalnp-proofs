import ThresholdFactorNetwork
import ThresholdSharedFlow

open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
  ThresholdFactorExpr ThresholdFactorRecipe
namespace ThresholdSharedPairErase

private theorem erase_or (xs : List Nat) (x : Nat) (R : Nat → Bool) (hit : x∈xs) :
    (R x || (xs.erase x).any R)=xs.any R := by
  induction xs with
  | nil => simp at hit
  | cons a as ih =>
    by_cases same : a=x
    · subst a; simp
    · have ha : x∈as := (List.mem_cons.mp hit).resolve_left (Ne.symm same)
      rw [List.erase_cons_tail (by simpa using same : ¬(a == x)),List.any_cons,List.any_cons,←ih ha]
      exact Bool.or_left_comm _ _ _

private theorem cost_zero (xs : List Nat) (f : Nat → Term) (h : ∀ i,(f i).cost=0) :
    ((xs.map f).map Term.cost).sum=0 := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons,List.sum_cons,h,zero_add,ih]

private theorem disj_available {n : Nat} {seen : List Nat} (xs : List Term)
    (av : ∀ q∈xs, Term.Avail n seen q) (t : Term) (ht : disj xs=some t) :
    Term.Avail n seen t := by
  induction xs generalizing t with
  | nil => simp [disj] at ht
  | cons a as ih =>
    have left := av a (by simp)
    cases e : disj as with
    | none =>
      have eq : a=t := by simpa [disj,e] using ht
      simpa [←eq] using left
    | some u =>
      have eq : Term.node .or a u=t := by simpa [disj,e] using ht
      rw [←eq]
      exact ⟨left,ih (fun q h => av q (by simp [h])) u e⟩

/-- Local term for a selective block replacement, preserving external wire IDs. -/
theorem recipe (x e : Nat) (t : Tree) (hit : x∈t.raws) (he : e∈t.exts) :
    ∃ q : Term, disj (residual x t)=some q ∧ q.cost+1=t.gates.length ∧
      (∀ (R S : Nat → Bool), (R x=true → S e=true) →
        q.value R S=(t.raws.any R || t.exts.any S)) ∧
      (∀ (n : Nat) (seen : List Nat), (∀ i∈t.raws, i<n) →
        (∀ i∈t.exts, i∈seen) → Term.Avail n seen q) := by
  have sz : (residual x t).length=t.gates.length := by
    have := t.slots
    have := List.length_pos_of_mem hit
    simp [residual,List.length_erase_of_mem hit]; omega
  have zero : ((residual x t).map Term.cost).sum=0 := by
    unfold residual
    rw [List.map_append,List.sum_append,cost_zero _ _ (fun _ => rfl),
        cost_zero _ _ (fun _ => rfl)]
  have c := disj_cost (residual x t)
  cases eq : disj (residual x t) with
  | none =>
    rw [eq] at c
    have mem : Term.ref e∈residual x t := by simp [residual,he]
    simp [c] at mem
  | some q =>
    refine ⟨q,(by first | exact eq | rfl),?_,?_,?_⟩
    · simpa [eq,zero,sz] using c
    · intro R S force
      have sem := disj_sem R S (residual x t)
      rw [eq] at sem
      simp only [valOpt,residual,List.any_append,List.any_map,Function.comp_def,Term.value] at sem
      rw [←erase_or _ x R hit]
      cases h : R x with
      | false => simpa [h] using sem
      | true =>
        have ae : t.exts.any S=true := List.any_eq_true.mpr ⟨e,he,force h⟩
        simpa [h,ae] using sem
    · intro n seen hr hs
      apply disj_available _ _ _ eq
      intro a ha
      rcases List.mem_append.mp ha with h|h
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
        exact hr i (List.mem_of_mem_erase hi)
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
        exact hs i hi

open T2OrPartition ThresholdSharedFlow

/-- Every physically evaluated wire dominating a forced U dominates its probe.
This statement intentionally does not constrain the ordinary raw bits. -/
theorem probe_le_actual {C : Circuit} {n : Nat} (L : Layout C n) (U : Id C)
    (ordinary : Nat → Bool)
    (row : ∀ i : Id C, ordinary (n+i.val)=act (L.op i)
      (ordinary (L.left i)) (ordinary (L.right i)))
    (forced : ordinary (n+U.val)=true) (w : Nat)
    (lit : on L U w=true) : ordinary w=true := by
  rw [on] at lit
  split at lit
  · contradiction
  · rename_i hn
    split at lit
    · rename_i b
      let i : Id C := ⟨w-n,b⟩
      have id : n+i.val=w := by dsimp [i]; omega
      have hl := (L.atIndex i).leftEarlier
      have hr := (L.atIndex i).rightEarlier
      rw [id] at hl hr
      by_cases same : i=U
      · simpa [←id,same] using forced
      · change (if i=U then true else _) = true at lit
        rw [if_neg same] at lit
        change (match L.op i with
          | .and => on L U (L.left i) && on L U (L.right i)
          | .or => on L U (L.left i) || on L U (L.right i)) = true at lit
        rw [←id,row i]
        cases op : L.op i with
        | and =>
          have h : on L U (L.left i)=true ∧ on L U (L.right i)=true := by simpa [op] using lit
          simp [act,probe_le_actual L U ordinary row forced (L.left i) h.1,
            probe_le_actual L U ordinary row forced (L.right i) h.2]
        | or =>
          have h : on L U (L.left i)=true ∨ on L U (L.right i)=true := by simpa [op] using lit
          rcases h with h|h
          · simp [act,probe_le_actual L U ordinary row forced (L.left i) h]
          · simp [act,probe_le_actual L U ordinary row forced (L.right i) h]
    · contradiction
termination_by w
decreasing_by all_goals dsimp [i] at hl hr ⊢ <;> omega

/-- A zero-raw lit probe in a group needs an external leaf unless the
overridden gate is itself one of the group's physical OR joins. -/
theorem lit_external {C : Circuit} {n : Nat} (L : Layout C n) (U : Id C)
    (t : Tree) (checked : t.Checked C n) (outside : n+U.val ∉ t.gates)
    (lit : on L U t.out=true) : ∃ e∈t.exts,on L U e=true := by
  induction t with
  | raw w =>
    change w<n at checked
    change on L U w=true at lit
    rw [on] at lit
    simp [checked] at lit
  | external e => exact ⟨e,by simp [Tree.exts],lit⟩
  | join j a b ihA ihB =>
    rcases checked with ⟨gate,ca,cb⟩
    have ix : j-n<C.gates.length := by
      obtain ⟨⟨pre,post,h,idx⟩,_,_⟩ := gate
      simp [h,idx]
    let i : Id C := ⟨j-n,ix⟩
    have id : n+i.val=j := by
      obtain ⟨⟨pre,post,_,idx⟩,_,_⟩ := gate
      simp [i,idx]
    have hi : i≠U := by
      intro same
      apply outside
      simp [Tree.gates,←same,id]
    have atJ := L.atIndex i
    rw [id] at atJ
    have op : L.op i=.or := by
      have eq := (gate_lookup atJ).symm.trans (gate_lookup gate)
      have h := congrArg (fun o : Option Gate => o.map Gate.op) eq
      cases v : L.op i <;> simp_all [binary,gateOp]
    rw [op] at atJ
    have xy := or_operands_unique atJ gate
    have h := row_eq L U i
    rw [if_neg hi,op] at h
    change on L U j=true at lit
    change on L U (n+i.val)=_ at h
    rw [id,xy.1,xy.2] at h
    have choice : on L U a.out=true ∨ on L U b.out=true := by simpa [h] using lit
    rcases choice with ha|hb
    · obtain ⟨e,mem,yes⟩ := ihA ca (by intro m; exact outside (by simp [Tree.gates,m])) ha
      exact ⟨e,by simp [Tree.exts,mem],yes⟩
    · obtain ⟨e,mem,yes⟩ := ihB cb (by intro m; exact outside (by simp [Tree.gates,m])) hb
      exact ⟨e,by simp [Tree.exts,mem],yes⟩

open ThresholdFactorNetwork

private theorem valid_replace (n : Nat) (pre : List Job) (old : Job) (tail : List Job)
    (q : Term) (seen : List Nat) (v : valid n seen (pre++old::tail))
    (a : q.Avail n (seenAfter pre seen)) :
    valid n seen (pre++(⟨old.output,q⟩ : Job)::tail) := by
  induction pre generalizing seen with
  | nil => exact ⟨a,v.2⟩
  | cons j js ih => exact ⟨v.1,ih (j.output::seen) v.2 a⟩

/-- A chronological one-block replacement. All old output identifiers,
including subsequent external references, are retained. -/
theorem selective_program {α : Type} {n : Nat} {raw : α → List Bool}
    {spec : α → Nat → Bool} (arity : ∀ a,(raw a).length=n)
    (pre : List Job) (old : Job) (tail : List Job) (q : Term) (seen : List Nat)
    (W : Work n raw spec seen) (v : valid n seen (pre++old::tail))
    (av : q.Avail n (seenAfter pre seen)) (saved : q.cost+1=old.term.cost)
    (prior : ∀ j∈pre++old::tail,∀ a,
        j.term.value (fun i => (raw a).getD i false) (spec a)=spec a j.output)
    (localOK : ∀ a,q.value (fun i => (raw a).getD i false) (spec a)=spec a old.output) :
    let js := pre++(⟨old.output,q⟩ : Job)::tail
    ∃ F : Work n raw spec (seenAfter js seen),
      F.gs.length+1=W.gs.length+((pre++old::tail).map (fun j => j.term.cost)).sum := by
  let new : Job := ⟨old.output,q⟩
  have ok : valid n seen (pre++new::tail) := valid_replace n pre old tail q seen v av
  have sem : ∀ j∈pre++new::tail,∀ a,
      j.term.value (fun i => (raw a).getD i false) (spec a)=spec a j.output := by
    intro j hj a
    rcases List.mem_append.mp hj with h|h
    · exact prior j (List.mem_append.mpr (Or.inl h)) a
    · rcases List.mem_cons.mp h with e|h
      · subst j; exact localOK a
      · exact prior j (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))) a
  obtain ⟨F,cost⟩ := program arity _ seen W ok sem
  refine ⟨F,?_⟩
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons] at cost ⊢
  change q.cost+1=old.term.cost at saved
  dsimp [new] at cost
  omega

end ThresholdSharedPairErase
