import ThresholdPivotWitness
import ThresholdEndpointPorts
import ThresholdReceiverPortUse
import ThresholdPrivateOwners
import ThresholdQuarterRetention
import ThresholdEffectiveColumns
import ThresholdSharedPairErase
namespace ThresholdPrivateElimination
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdOrGroups T2OrPartition
open ThresholdFirstActive ThresholdRegularSource ThresholdSimpleIncidence T2SoleOrSplice
open ThresholdSecondaryReceivers ThresholdLeakPins
open private root_trace from ThresholdPathEndpoints
variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- Before an AND fires the OR-only path ends at an original raw-bearing
row or exactly one private receiver downstream. -/
private theorem two_layers (reg : MeetsInternal L) (x : Fin n)
    (quiet : ∀ r∈endpoints L x, ∀ v∈signature C n r, ¬ReadsOR L (n+v.val))
    (i : Id C) (stop : next C n i=none) (path : OrPath L x (n+i.val)) :
    i∈endpoints L x ∨ ∃ r∈endpoints L x,i∈signature C n r := by
  rcases root_trace i stop path with h|⟨w,hw,read,walk⟩
  · exact Or.inl h
  · obtain ⟨⟨d,ds,wd⟩,lt⟩ := root_externals L reg Fin.val i w hw
    subst w
    have result := two_layers reg x quiet d ds walk
    rcases result with row|⟨r,hr,rec⟩
    · obtain ⟨j,hj,eq⟩ := receiver_use L Fin.val d (makeBlock L Fin.val i)
        (mem_roots L Fin.val i stop) hw
      have same : i=j := Fin.ext (Nat.add_left_cancel ((makeBlock_out L Fin.val i).symm.trans eq))
      exact Or.inr ⟨d,row,same.symm ▸ hj⟩
    · exact False.elim (quiet r hr d rec read)
termination_by i.val
decreasing_by omega

theorem path_selected (reg : MeetsInternal L) (x : Fin n) (H : Finset (Id C))
    (rows : endpoints L x⊆good C n H) (pick : Id C→Bool)
    (quiet : ∀ r∈endpoints L x, ∀ v∈signature C n r, ¬ReadsOR L (n+v.val))
    (selected : ∀ r∈endpoints L x, ∀ v∈signature C n r, ∀ j b,
      L.op j=.and → port L j b=n+v.val → pick j=b)
    (i : Id C) (op : L.op i=.and) (b : Bool) (path : OrPath L x (port L i b)) : pick i=b := by
  have mem : port L i b∈(makeBlock L Fin.val i).exts := by
    unfold makeBlock
    split
    · cases b <;> simp [Block.exts,port]
    · rename_i e; simp [op] at e
  obtain ⟨⟨r,stop,wd⟩,_⟩ := root_externals L reg Fin.val i _ mem
  rcases two_layers L reg x quiet r stop (wd ▸ path) with direct|⟨u,hu,hr⟩
  · have reader : i∈readers C (n+r.val) := by
      apply read_mem
      rw [layout_inputs (L.atIndex i)]
      cases b <;> simp_all [port]
    have wrong := (physical_op L i).mp ((Finset.mem_filter.mp (rows direct)).2.2 i reader)
    rw [op] at wrong
    contradiction
  · exact selected u hu r hr i b op wd

theorem at_most_one (correct : Computes n C) (bound : C.output<n+C.gates.length)
    (E : Finset (Fin n)) (pick : Id C→Bool)
    (track : ∀ x∈E,∀ i,L.op i=.and → ∀ b,OrPath L x (port L i b) → pick i=b) :
    E.card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra ne
  obtain ⟨j,on⟩ := pair_active L correct bound x y ne
  let rec never (i : Id C) : ¬Active L {x,y} i := by
    intro ai
    have side (b : Bool) : pick i=b := by
      have ev := (L.atIndex i).eval (vector {x,y}) (by simp [vector])
      rw [ai.1] at ev
      have hit := ai.2
      unfold bit at hit
      rw [ev] at hit
      have lit : bit C {x,y} (port L i b)=true := by cases b <;> simp_all [port,bit,ResidualSurplus.act]
      have lt : port L i b<n+i.val := by
        cases b
        · exact (L.atIndex i).leftEarlier
        · exact (L.atIndex i).rightEarlier
      have fit := i.isLt
      rcases provenance L {x,y} _ (by omega) lit with ⟨z,hz,p⟩|⟨j,le,on⟩
      · have a : z=x ∨ z=y := by simpa using hz
        rcases a with rfl|rfl
        · exact track _ hx i ai.1 b p
        · exact track _ hy i ai.1 b p
      · exact False.elim (never j on)
    exact Bool.noConfusion ((side false).symm.trans (side true))
  termination_by i.val
  decreasing_by omega
  exact never j on
open private owner_or from ThresholdReceiverCounts

theorem private_socket (M : LexMinimum n C) (H : Finset (Id C)) (x : Fin n) (r v : Id C)
    (row : r∈good C n H) (hit : r∈endpoints L x) (rec : v∈signature C n r)
    (low : v∉ThresholdSharedPartition.hubs C n) :
    ∃ q : Pin C, Assigned L v q ∧
      (∀ p, ThresholdEffectiveColumns.feeds L v p → p=q) ∧ ¬ReadsOR L (n+v.val) := by
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp rec)
  have org := owner_or (n:=n) j ((Finset.mem_filter.mp row).2.2 j hj)
  have stop := (owner_spec C n j).2
  rw [eq] at org stop
  have hot := ThresholdStarBypass.endpoint_hot L {x} x r (by simp) hit
  have vh := ThresholdSharedPairErase.probe_le_actual L r
    (fun w => (C.wires (vector {x})).getD w false)
    (fun i => (L.atIndex i).eval _ (by simp [vector])) hot _ (receiver_later L row rec).2
  have out : C.output≠n+v.val := by
    intro h
    rw [←h] at vh
    have impossible := (M.eligible.1 {x}).mp vh
    simp at impossible
  have notmany : ¬2≤(readers C (n+v.val)).length := by
    intro many
    exact low (by simp [ThresholdSharedPartition.hubs,ThresholdSharedOrBudget.sharedOrs,
      ThresholdSharedOrBudget.sharedGates,org,many])
  obtain ⟨p,feed,later,unique⟩ := ThresholdEffectiveColumns.unmarked_step L M v (by
    rintro (a|b); exact out a; exact notmany b)
  have mem := ThresholdEffectiveColumns.feeds_reader L feed
  have only : readers C (n+v.val)=[p.1] := by
    cases e : readers C (n+v.val) with
    | nil => simp [e] at mem
    | cons j rest => cases rest with
      | nil => simpa [e] using congrArg (fun q : Id C => [q]) (List.mem_singleton.mp (e ▸ mem)).symm
      | cons j' rest => simp [e] at notmany
  have non := ThresholdFanoutBudget.singleton_target stop org out only later
  have op : L.op p.1=.and := by
    cases h : L.op p.1 with
    | and => rfl
    | or => have yes := (physical_op L _).mpr h; simp_all
  have porteq : port L p.1 p.2=n+v.val := by cases p with | mk i b => cases b <;> exact feed
  refine ⟨p,⟨op,porteq⟩,unique,?_⟩
  rintro ⟨i,oi,h|h⟩
  · have r := unique (i,false) h
    have bad := congrArg (fun q : Pin C => L.op q.1) r
    simp_all
  · have r := unique (i,true) h
    have bad := congrArg (fun q : Pin C => L.op q.1) r
    simp_all

/-- Localized to the two receiver columns of each retained row. Every actual
pair inside that set must be an image of an original raw input. -/
theorem one_pair (M : LexMinimum n C) (reg : MeetsInternal L)
    (bound : C.output<n+C.gates.length) (H S : Finset (Id C)) (sg : S⊆good C n H)
    (pick : Id C→Bool)
    (quiet : ∀ r∈S, ∀ v∈signature C n r, ¬ReadsOR L (n+v.val))
    (selected : ∀ r∈S, ∀ v∈signature C n r, ∀ j b,
      L.op j=.and → port L j b=n+v.val → pick j=b) :
    (S.powersetCard 2 ∩ (Finset.univ : Finset (Fin n)).image (endpoints L)).card≤1 := by
  classical
  let E := (Finset.univ : Finset (Fin n)).filter (fun x => endpoints L x⊆S)
  have cap := at_most_one L M.eligible.1 bound E pick (by
    intro x hx
    have sub := (Finset.mem_filter.mp hx).2
    exact path_selected L reg x H (fun i hi => sg (sub hi)) pick
      (fun i hi => quiet i (sub hi)) (fun i hi => selected i (sub hi)))
  have incl : S.powersetCard 2 ∩ (Finset.univ : Finset (Fin n)).image (endpoints L)
      ⊆ E.image (endpoints L) := by
    intro p hp
    obtain ⟨ps,raw⟩ := Finset.mem_inter.mp hp
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp raw
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_powersetCard.mp ps).1⟩,rfl⟩
  exact (Finset.card_le_card incl).trans ((Finset.card_image_le).trans cap)
end ThresholdPrivateElimination
