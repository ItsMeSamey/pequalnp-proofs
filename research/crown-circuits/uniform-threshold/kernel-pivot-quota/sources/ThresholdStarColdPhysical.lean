import ThresholdStarSiteShield
import ThresholdStarOpposite
import ThresholdStarAlias
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RegularOrDelete T2SoleOrSplice T2CubeDeletion
open ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence
open ThresholdSharedPartition ThresholdSharedFlow T2OrPartition

theorem cold_structure {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (u : Id (source gs out)) (hu : u∈hubs (source gs out) n)
    (two : ∀ x,(endpoints (layout n gs out M.eligible) x).card=2)
    (inj : Function.Injective (endpoints (layout n gs out M.eligible)))
    (S : Finset (Fin n)) (size : 2<S.card)
    (P : ∀ x : S,PrivateSite (layout n gs out M.eligible) u x.val)
    : (∀ a:S, active (layout n gs out M.eligible) u (P a).v=false) ∧
      ∀ x y:S, on (layout n gs out M.eligible) u (P x).other=false →
        on (layout n gs out M.eligible) u (P y).other=false → x=y := by
  classical
  let C := source gs out
  let L := layout n gs out M.eligible
  let bs := forest L Fin.val
  let sel := fun w : Nat => decide (∃ x:S,w=n+(P x).v.val)
  let raw := fun (s : Finset (Fin n)) (j : Nat) => (vector s).getD j false
  let zero : Env := fun _ => false
  let snap := fun s => run (n+u.val) sel true (raw s) bs zero
  have incident (a : Fin n) (ha : a∈S) : u∈endpoints L a := by
    rw [(P ⟨a,ha⟩).pair]; simp
  have pick (a b : Fin n) : ∃ z∈S,z≠a ∧ z≠b := by
    by_contra! none
    have sub : S⊆{a,b} := by
      intro z hz
      by_cases e : z=a
      · simp [e]
      · simp [none z hz e]
    have card := Finset.card_le_card sub
    by_cases e : a=b <;> simp [e] at card <;> omega
  have selected (p : Nat) (t : Tree) (_ : Block.group p t∈bs) (_ : t.out≠n+u.val)
      (on : sel t.out=true) : ∃ (a b : Fin n) (v : Id C),
        a∈S ∧ b∈S ∧ a≠b ∧ endpoints L a⊆{u,v} ∧ t.out=n+v.val := by
    obtain ⟨a,ha⟩ : ∃ a:S,t.out=n+(P a).v.val := of_decide_eq_true on
    obtain ⟨b,hb,ne,_⟩ := pick a a
    exact ⟨a,b,(P a).v,a.property,hb,Ne.symm ne,by rw [(P a).pair],ha⟩
  have trace (s : Finset (Fin n)) (inStar : s⊆S) :=
    promoted_threshold_trace M reg sel u S (Finset.card_pos.mp (by omega)) incident selected s inStar
  have emptyTaps : taps (n+u.val) sel (raw ∅) bs zero=false :=
    (trace ∅ (by simp)).2 (by simp)
  have rr := regular_inputs n gs out M.eligible reg
  have bk := (physical_book L rr.1 Fin.val rr.2.1 rr.2.2).1
  have hub : u∈ThresholdSharedOrBudget.sharedOrs C n := by simpa [hubs] using hu
  have gate := ThresholdSharedOrBudget.shared_stops (List.mem_filter.mp hub).1
  have op := (physical_op L u).mp (List.mem_filter.mp hub).2
  obtain ⟨A,ha,outU,gateU⟩ := hub_center L u gate op
  have raw0 : raw ∅=zero := by funext j; change (vector (∅ : Finset (Fin n))).getD j false=false; rw [vec_get]; split <;> simp
  have bridge (j : Nat) (hj : j∈outputs bs []) : snap ∅ j=on L u j := by
    change run _ _ _ _ _ _ _=_
    rw [run_eq_of_no_tap _ _ _ _ _ emptyTaps,raw0]
    exact probe_book L u A ha outU gateU sel bs [] (fun _ h => h) bk zero (by simp) j hj
  have aliasCold (a : S) (z : Fin n) (hz : z∈S) (ne : a.val≠z) :
      snap {z} (n+(P a).v.val)=false := by
    obtain ⟨p,t,mem,rt⟩ := (P a).group
    obtain ⟨pre,post,split⟩ := List.append_of_mem mem
    exact alias_singleton_cold L u (P a).v (P a).distinct a z ne (P a).pair (incident z hz)
      (two z) inj sel (decide_eq_true ⟨a,rfl⟩) pre post p t split rt
  have ok (a : S) (r : Finset (Fin n)) (d : snap r (P a).other=false) :=
    (P a).shield sel (raw r) zero d
  have admits (a : S) (z : Fin n) (hz : z∈S) (ne : a.val≠z) : snap {z} (P a).other=true := by
    apply partner_admits bs (n+u.val) (n+(P a).v.val) out sel a z ne (P a).other zero
    · intro h; exact (ok a {z} h).1
    · intro b hb
      cases b with
      | meet => trivial
      | group p t =>
        intro _ _
        apply ThresholdFactorCut.physical_no_other L Fin.val (P a).z (P a).consumer (P a).alone _ hb
        intro eq
        have bad : Block.group p t = Block.meet (n+(P a).z.val) (L.left (P a).z) (L.right (P a).z) :=
          List.inj_on_of_nodup_map (ThresholdFactorCut.output_nodup L Fin.val) hb (P a).meet eq
        contradiction
    · exact (P a).noOutput
    · intro s hs
      have sub : s⊆S := by
        rcases hs with rfl|rfl
        · exact Finset.singleton_subset_iff.mpr hz
        · exact Finset.insert_subset a.property (Finset.singleton_subset_iff.mpr hz)
      exact (trace s sub).1
  have cold (a:S) (c : on L u (P a).other=false) : snap ∅ (P a).other=false :=
    (bridge _ ((P a).probe_stored bk).2).trans c
  constructor
  · intro a
    obtain ⟨z,sz,zx,_⟩ := pick a a
    have rise : Below (raw ∅) (raw {z}) := by
      intro j
      rw [raw0]
      change false=true → _
      simp
    have dom := scan_monotone (n+u.val) sel true _ _ rise bs zero zero (fun _ h => h)
    have az := aliasCold a z sz (Ne.symm zx)
    change on L u (n+(P a).v.val)=false
    rw [←bridge _ ((P a).probe_stored bk).1]
    cases h : snap ∅ (n+(P a).v.val) with
    | false => rfl
    | true =>
      have lit : snap {z} (n+(P a).v.val)=true := dom _ h
      rw [az] at lit
      contradiction
  intro x y coldX coldY
  by_contra different
  have xy : x.val≠y.val := fun e => different (Subtype.ext e)
  have dx := cold x coldX
  have dy := cold y coldY
  have quiet : Away (n+(P x).v.val) (snap ∅) (snap {x.val}) := by
    have away : Away x.val (raw ∅) (raw {x.val}) := by
      simpa only [raw,Away,Finset.insert_empty] using (off_insert (∅ : Finset (Fin n)) x.val).2
    exact shielded_quiet _ _ _ _ _ _ away _ zero zero (fun _ _ => rfl) (ok x ∅ dx).1
  have yx := admits y x x.property (Ne.symm xy)
  have must : (P y).other=n+(P x).v.val := by
    by_contra ne
    have same := quiet _ ne
    rw [dy,yx] at same
    contradiction
  obtain ⟨z,sz,zx,zy⟩ := pick x y
  have yz := admits y z sz (Ne.symm zy)
  rw [must,aliasCold x z sz (Ne.symm zx)] at yz
  contradiction

#print axioms cold_structure
end ThresholdStarBypass
