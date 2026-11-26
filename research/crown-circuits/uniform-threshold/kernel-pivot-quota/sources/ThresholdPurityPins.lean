import ThresholdPivotWitness
import ThresholdPrivateOwners
import ThresholdHighComponents
import ThresholdHubDeficits
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdOrGroups T2OrPartition
namespace ThresholdPurityPins
open ThresholdLeakPins ThresholdSimpleIncidence ThresholdRegularSource ThresholdPrivateOwners
open ThresholdHubDegrees ThresholdSharedPartition ThresholdSharedOrBudget ThresholdSecondaryReceivers
open ThresholdFanoutBudget ThresholdSharedFlow
open private count_ports pin_of_read from ThresholdPivotWitness
variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- Each private neighbor of u is a different stopped OR root. No bound on
the degree or number of raw leaves of that root is used. -/
theorem single_le_private (u : Id C) (two : ∀ x,(endpoints L x).card=2)
    (inj : Function.Injective (endpoints L)) : (singleAt L u).card≤(privateRoots C n).card := by
  classical
  have witness (x) (hx : x∈singleAt L u) : ∃ v∈privateRoots C n,endpoints L x={u,v} := by
    have hits : hits L x={u} := (Finset.mem_filter.mp hx).2
    have ux : u∈endpoints L x := Finset.mem_of_mem_inter_left (show u∈ThresholdSharedPartition.hits L x by simp [hits])
    obtain ⟨v,w,vw,pair⟩ := Finset.card_eq_two.mp (two x)
    have z : ∃ d,d≠u ∧ endpoints L x={u,d} := by
      rw [pair] at ux
      rcases Finset.mem_insert.mp ux with rfl|eq
      · exact ⟨w,vw.symm,pair⟩
      · obtain rfl := Finset.mem_singleton.mp eq
        exact ⟨v,vw,pair.trans (Finset.pair_comm _ _)⟩
    obtain ⟨d,du,ed⟩ := z
    have dx : d∈endpoints L x := by simp [ed]
    have stop := (ThresholdPivotWitness.endpoint_pin L x d dx).1
    have no : d∉hubs C n := fun h => du (Finset.mem_singleton.mp (hits ▸ Finset.mem_inter.mpr ⟨dx,h⟩))
    have raw : x.val∈rawList (makeBlock L Fin.val d) := by simpa [endpoints,labels,stop] using dx
    have org : isOr C d=true := by
      apply (physical_op L d).mpr
      unfold makeBlock at raw
      split at raw
      · simp [rawList] at raw
      · assumption
    exact ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,stop,org,no⟩,ed⟩
  rw [←show (singleAt L u).attach.card=(singleAt L u).card from Finset.card_attach]
  apply Finset.card_le_card_of_injOn (fun x : ↥(singleAt L u) => (witness x.val x.property).choose)
  · exact fun x _ => (witness x.val x.property).choose_spec.1
  · intro x _ y _ eq
    apply Subtype.ext
    apply inj
    exact (witness x.val x.property).choose_spec.2.trans
      ((congrArg (fun v : Id C => ({u,v} : Finset (Id C))) eq).trans
        (witness y.val y.property).choose_spec.2.symm)

noncomputable def impure (H : Finset (Id C)) := H.filter (fun i => (makeBlock L Fin.val i).exts≠[])
noncomputable def interior (C : Circuit) (n : Nat) := Finset.univ.filter (fun i : Id C => (next C n i).isSome)

private theorem hub_stop {i : Id C} (hi : i∈hubs C n) : next C n i=none :=
  shared_stops (List.mem_filter.mp (List.mem_toFinset.mp hi)).1

private theorem hub_or {i : Id C} (hi : i∈hubs C n) : isOr C i=true :=
  (List.mem_filter.mp (List.mem_toFinset.mp hi)).2

/-- An impure high root has a physical operand with a stopped non-high source.
The chosen operand's OR-tree owner is the root itself, so different roots get
different operands. A high wire entering a high OR root would light that root
on the source probe regardless of other incoming values. -/
private theorem impurity_witness (reg : MeetsInternal L) (H : Finset (Id C)) (sub : H⊆hubs C n)
    (anti : ∀ u∈H,∀ v∈H,u≠v → active L u v=false)
    (v : Id C) (vimp : v∈impure L H) :
    ∃ p : Pin C, owner C n p.1=v ∧ ∃ d : Id C,source L p=n+d.val ∧
      next C n d=none ∧ d∉H := by
  obtain ⟨vh,ne⟩ := Finset.mem_filter.mp vimp
  have stop := hub_stop (sub vh)
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ ne
  obtain ⟨⟨d,ds,wd⟩,lt⟩ := root_externals L reg Fin.val v w hw
  subst w
  obtain ⟨r,hr,eq⟩ := receiver_use L Fin.val d (makeBlock L Fin.val v) (mem_roots L Fin.val v stop) hw
  have vr : v=r := Fin.ext (Nat.add_left_cancel ((makeBlock_out L Fin.val v).symm.trans eq))
  subst r
  obtain ⟨i,reader,ow⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
  have op : isOr C i=true := by
    by_contra h
    have oi : L.op i=.and := by
      cases tag : L.op i with
      | and => rfl
      | or => exact False.elim (h ((physical_op L i).mpr tag))
    have ni : next C n i=none := by
      cases z : next C n i with
      | none => rfl
      | some j => have wrong := (physical_op L i).mp (next_is_or z).1; simp_all
    have iv : i=v := (owner_of_stop C n i ni).symm.trans ow
    exact h (by simpa only [iv] using hub_or (sub vh))
  obtain ⟨b,pb⟩ := pin_of_read L i _ (reader_pin reader)
  refine ⟨(i,b),ow,d,pb,ds,?_⟩
  intro dh
  have dd : active L d d=true := by simp [row_eq]
  have on : active L d i=true := or_carry L (reader_pin reader) op dd
  have vv := owner_carry L d i on
  rw [ow] at vv
  have different : d≠v := fun e => by subst d; omega
  have off := anti d dh v vh different
  simp_all

private def number (C : Circuit) (n : Nat) : Id C ↪ Nat :=
  ⟨fun i => n+i.val,fun _ _ h => Fin.ext (Nat.add_left_cancel h)⟩

private theorem priced (W : Finset Nat) (d : Nat) (reads : ∀ w∈W,d≤(readers C w).length) :
    d*W.card≤(Finset.univ.filter (fun p : Pin C => source L p∈W)).card := by
  classical
  rw [←Finset.sum_card_fiberwise_eq_card_filter Finset.univ W (source L)]
  calc
    _ = ∑ w∈W,d := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun w hw => (reads w hw).trans_eq (count_ports L w).symm)

/-- Count four disjoint classes of actual physical operand occurrences. -/
theorem physical_budget (reg : MeetsInternal L) (H : Finset (Id C)) (sub : H⊆hubs C n)
    (anti : ∀ u∈H,∀ v∈H,u≠v → active L u v=false)
    (twice : ∀ x : Fin n,(readers C x.val).length=2) :
    2*n+(interior C n).card+2*H.card+(impure L H).card≤2*C.gates.length := by
  classical
  let R := Finset.range n
  let I := (interior C n).map (number C n)
  let Q := H.map (number C n)
  let slots := fun W : Finset Nat => Finset.univ.filter (fun p : Pin C => source L p∈W)
  have raw : 2*n ≤ (slots R).card := by
    simpa only [R,Finset.card_range] using priced L R 2 (fun w hw => (twice ⟨w,Finset.mem_range.mp hw⟩).ge)
  have inner : (interior C n).card ≤ (slots I).card := by
    have step := priced L I 1 (by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
      have flag := (Finset.mem_filter.mp hi).2
      cases z : next C n i with
      | none => simp [z] at flag
      | some j =>
        change 1≤(readers C (n+i.val)).length
        simp [next_readers z])
    simpa only [I,Finset.card_map,one_mul,slots] using step
  have high : 2*H.card ≤ (slots Q).card := by
    have step := priced L Q 2 (by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
      have h := (List.mem_filter.mp (List.mem_toFinset.mp (sub hi))).1
      change 2≤(readers C (n+i.val)).length
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp h).2)
    simpa only [Q,Finset.card_map,slots] using step
  let alloc := fun i (h : i∈impure L H) => (impurity_witness L reg H sub anti i h).choose
  let J := (impure L H).attach.image (fun i => alloc i.val i.property)
  have inv (i) (hi : i∈impure L H) := (impurity_witness L reg H sub anti i hi).choose_spec
  have cj : J.card=(impure L H).card := by
    change ((impure L H).attach.image _).card=_
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro a b eq
      exact Subtype.ext (((inv _ a.property).1.symm.trans
        (congrArg (fun p : Pin C => owner C n p.1) eq)).trans (inv _ b.property).1)
  have ri : Disjoint (slots R) (slots I) := by
    apply Finset.disjoint_left.mpr
    intro p r i
    obtain ⟨v,_,eq⟩ := Finset.mem_map.mp (Finset.mem_filter.mp i).2
    have a := Finset.mem_range.mp (Finset.mem_filter.mp r).2
    change n+v.val=source L p at eq
    omega
  have rh : Disjoint (slots R) (slots Q) := by
    apply Finset.disjoint_left.mpr
    intro p r i
    obtain ⟨v,_,eq⟩ := Finset.mem_map.mp (Finset.mem_filter.mp i).2
    have a := Finset.mem_range.mp (Finset.mem_filter.mp r).2
    change n+v.val=source L p at eq
    omega
  have ih : Disjoint (slots I) (slots Q) := by
    apply Finset.disjoint_left.mpr
    intro p i h
    obtain ⟨a,ai,ea⟩ := Finset.mem_map.mp (Finset.mem_filter.mp i).2
    obtain ⟨b,bh,eb⟩ := Finset.mem_map.mp (Finset.mem_filter.mp h).2
    have ab := (number C n).injective (ea.trans eb.symm)
    subst b
    have z := (Finset.mem_filter.mp ai).2
    simp [hub_stop (sub bh)] at z
  have sep : Disjoint ((slots R ∪ slots I) ∪ slots Q) J := by
    apply Finset.disjoint_left.mpr
    intro p hp j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp j
    obtain ⟨_,d,eq,stop,nh⟩ := inv _ i.property
    rcases Finset.mem_union.mp hp with ri|high
    · rcases Finset.mem_union.mp ri with r|i
      · have lt := Finset.mem_range.mp (Finset.mem_filter.mp r).2
        change source L (alloc i.val i.property) = n+d.val at eq
        omega
      · obtain ⟨v,vi,ev⟩ := Finset.mem_map.mp (Finset.mem_filter.mp i).2
        have vd : v=d := (number C n).injective (ev.trans eq)
        subst v
        have imp := (Finset.mem_filter.mp vi).2
        simp [stop] at imp
    · obtain ⟨v,vh,ev⟩ := Finset.mem_map.mp (Finset.mem_filter.mp high).2
      exact nh ((number C n).injective (ev.trans eq) ▸ vh)
  have cap := Finset.card_le_card (Finset.subset_univ (((slots R ∪ slots I) ∪ slots Q) ∪ J))
  rw [Finset.card_union_of_disjoint sep,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨rh,ih⟩),
    Finset.card_union_of_disjoint ri,cj] at cap
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at cap
  omega

theorem gate_cover (C : Circuit) (n : Nat) :
    C.gates.length≤(interior C n).card+(hubs C n).card+(privateRoots C n).card+(andIds C).length := by
  classical
  let I := interior C n
  let H := hubs C n
  let P := privateRoots C n
  let A := (andIds C).toFinset
  have all : (Finset.univ : Finset (Id C))⊆I∪H∪P∪A := by
    intro i _
    by_cases org : isOr C i=true
    · cases e : next C n i with
      | some j =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [e]⟩)))
      | none =>
        by_cases h : i∈H
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,org,h⟩))
    · exact Finset.mem_union_right _ (by simp [A,andIds,org])
  have bound := Finset.card_le_card all
  have a := Finset.card_union_le (I∪H∪P) A
  have b := Finset.card_union_le (I∪H) P
  have c := Finset.card_union_le I H
  have d : A.card≤(andIds C).length := List.toFinset_card_le _
  simp only [Finset.card_univ,Fintype.card_fin] at bound
  change C.gates.length≤I.card+H.card+P.card+(andIds C).length
  omega

open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdHighComponents
theorem regular_impurity {n out : Nat} {gs : List ResidualSurplus.Raw}
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    2*n + 2*(high L).card + (impure L (high L)).card ≤
      C.gates.length+(hubs C n).card+(privateRoots C n).card+(andIds C).length := by
  intro C L
  obtain ⟨internal,twice,_⟩ := regular_inputs n gs out M.eligible reg
  have anti := ThresholdPhysicalIdeals.high_antichain M reg
  have hh : high L⊆hubs C n := Finset.filter_subset _ _
  have cap := physical_budget L internal (high L) hh (by
    intro u uh v vh ne
    cases h : active L u v with
    | false => rfl
    | true => exact False.elim (anti u uh v vh ((ThresholdPhysicalIdeals.mem_pair L u v).mpr
        ⟨⟨hh uh,hh vh⟩,ne,h⟩))) (fun x => twice x.val x.isLt)
  have cov := gate_cover C n
  dsimp only [C] at cap cov ⊢
  omega

open ThresholdHubDeficits
theorem regular_purity_product {n out : Nat} {gs : List ResidualSurplus.Raw}
    (hn : 5≤n) (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    let h : ℤ := (hubs C n).card
    let s := surplus n C.size
    let low : ℤ := ((hubs C n) \ high L).card
    h*((impure L (high L)).card:ℤ) ≤
      s^2+7*s+14-2*(n:ℤ)+h*(5*((andIds C).length:ℤ)+2*low-2) := by
  intro C L h s low
  let p : ℤ := (privateRoots C n).card
  let a : ℤ := (andIds C).length
  let d : ℤ := s+1-h
  let j : ℤ := (impure L (high L)).card
  have simple := classified_simple (by omega : 2≤n) M reg
  have structure' := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out M reg
  have row (u) (hu : u∈hubs C n) : d+3-p≤D L u := by
    have de := degrees_partition L u hu simple.1 simple.2.1
    have sp := row_space L u hu structure'.no_shared_raw
    have ex := single_le_private L u simple.1 simple.2.1
    dsimp only [d,s,h,p,D,C] at *
    omega
  have total := Finset.sum_le_sum row
  simp only [Finset.sum_const,nsmul_eq_mul] at total
  have delta : h*(d+3-p) ≤ s^2+7*s+14-2*(n:ℤ) :=
    le_trans total (regular_deficit_budget hn M reg).2
  have pr : p≤2*a+1 := by
    dsimp only [p,a,C]
    exact_mod_cast private_budget (L:=L) M
  have split := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset _ _ : high L⊆hubs C n)
  change ((hubs C n) \ high L).card+(high L).card=(hubs C n).card at split
  have slots := regular_impurity M reg
  have cnt : j≤d+3*a+2*low := by
    dsimp only [j,d,h,p,a,low,s,surplus]
    change 2*n+2*(high L).card+(impure L (high L)).card≤
      C.size+(hubs C n).card+(privateRoots C n).card+(andIds C).length at slots
    dsimp only [p,a] at pr
    dsimp only [C] at slots split pr ⊢
    omega
  have h0 : 0≤h := by dsimp [h]; positivity
  have compare := mul_le_mul_of_nonneg_left (show j≤(d+3-p)+(5*a+2*low-2) by omega) h0
  change h*j≤_+h*(5*a+2*low-2)
  rw [mul_add] at compare
  omega

end ThresholdPurityPins
