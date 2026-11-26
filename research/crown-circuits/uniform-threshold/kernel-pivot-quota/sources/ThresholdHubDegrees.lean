import ThresholdPublicSharp
import ThresholdProbeIdeals
namespace ThresholdHubDegrees
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence
open ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs T2OrPartition
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def raws (u : Id C) := Finset.univ.filter (fun x : Fin n => u∈endpoints L x)
noncomputable def neighbors (u : Id C) := (hubs C n).filter (fun v =>
  v≠u ∧ ∃ x : Fin n,endpoints L x={u,v})
noncomputable def before (u : Id C) := (hubs C n).filter (fun v => v≠u ∧ active L v u=true)
noncomputable def after (u : Id C) := (hubs C n).filter (fun v => u≠v ∧ active L u v=true)

theorem degrees_partition (u : Id C) (hu : u∈hubs C n)
    (two : ∀ x,(endpoints L x).card=2) (inj : Function.Injective (endpoints L)) :
    (raws L u).card=(singleAt L u).card+(neighbors L u).card := by
  classical
  let S := singleAt L u
  let R := raws L u
  let H := hubs C n
  let N := neighbors L u
  have inside : S⊆R := by
    intro x hx
    have he : hits L x={u} := (Finset.mem_filter.mp hx).2
    have mem : u∈hits L x := by simp [he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_of_mem_inter_left mem⟩
  have pick (x : Fin n) (hx : x∈R \ S) : ∃ v∈N,endpoints L x={u,v} := by
    obtain ⟨inR,outS⟩ := Finset.mem_sdiff.mp hx
    have ux : u∈endpoints L x := (Finset.mem_filter.mp inR).2
    obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp (two x)
    obtain ⟨v,vu,pair⟩ : ∃ v,v≠u ∧ endpoints L x={u,v} := by
      rw [eq] at ux
      rcases Finset.mem_insert.mp ux with same|other
      · subst a; exact ⟨b,Ne.symm ab,eq⟩
      · obtain rfl := Finset.mem_singleton.mp other
        exact ⟨a,ab,eq.trans (Finset.pair_comm _ _)⟩
    have vh : v∈H := by
      by_contra no
      apply outS
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change endpoints L x ∩ H={u}
      rw [pair]
      ext j
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨a|b,h⟩
        · exact a
        · subst j; exact False.elim (no h)
      · rintro rfl; exact ⟨Or.inl rfl,hu⟩
    exact ⟨v,Finset.mem_filter.mpr ⟨vh,vu,x,pair⟩,pair⟩
  have unique (v w : Id C) (uv : v≠u) (e : ({u,v} : Finset (Id C))={u,w}) : v=w := by
    have h : v∈({u,w} : Finset (Id C)) := e ▸ (by simp : v∈({u,v} : Finset (Id C)))
    simpa [uv] using h
  have card : (R \ S).card=N.card := by
    apply Finset.card_bij (fun x hx => (pick x hx).choose)
    · intro x hx; exact (pick x hx).choose_spec.1
    · intro x hx y hy e
      apply inj
      rw [(pick x hx).choose_spec.2,(pick y hy).choose_spec.2,e]
    · intro v hv
      obtain ⟨vh,vu,⟨x,pair⟩⟩ := Finset.mem_filter.mp hv
      have hx : x∈R \ S := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [pair]⟩,?_⟩
        intro hs
        have hit : hits L x={u} := (Finset.mem_filter.mp hs).2
        have ve : v∈hits L x := Finset.mem_inter.mpr ⟨by simp [pair],vh⟩
        exact vu (Finset.mem_singleton.mp (hit ▸ ve))
      refine ⟨x,hx,?_⟩
      have h := (pick x hx).choose_spec
      exact unique _ _ (Finset.mem_filter.mp h.1).2.1 (h.2.symm.trans pair)
  have split := Finset.card_sdiff_add_card_eq_card inside
  change R.card=S.card+N.card
  omega

theorem row_space (u : Id C) (hu : u∈hubs C n)
    (noedge : ∀ a∈hubs C n,∀ b∈hubs C n,a≠b → active L a b=true →
      ∀ x : Fin n,a∈endpoints L x → b∉endpoints L x) :
    (neighbors L u).card+(before L u).card+(after L u).card+1≤(hubs C n).card := by
  classical
  let N := neighbors L u
  let P := before L u
  let T := after L u
  have np : Disjoint N P := Finset.disjoint_left.mpr (by
    intro v nv pv
    obtain ⟨vh,vu,⟨x,eq⟩⟩ := Finset.mem_filter.mp nv
    exact noedge v vh u hu vu (Finset.mem_filter.mp pv).2.2 x (by simp [eq]) (by simp [eq]))
  have nt : Disjoint N T := Finset.disjoint_left.mpr (by
    intro v nv tv
    obtain ⟨vh,vu,⟨x,eq⟩⟩ := Finset.mem_filter.mp nv
    exact noedge u hu v vh (Ne.symm vu) (Finset.mem_filter.mp tv).2.2 x (by simp [eq]) (by simp [eq]))
  have pt : Disjoint P T := Finset.disjoint_left.mpr (by
    intro v pv tv
    obtain ⟨_,vu,on⟩ := Finset.mem_filter.mp pv
    have off := opposite_off L vu on
    have yes := (Finset.mem_filter.mp tv).2.2
    rw [off] at yes
    contradiction)
  have bound : N ∪ P ∪ T ⊆ (hubs C n).erase u := by
    intro v hv
    rcases Finset.mem_union.mp hv with head|last
    · rcases Finset.mem_union.mp head with hit|hit
      · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hit).2.1,(Finset.mem_filter.mp hit).1⟩
      · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hit).2.1,(Finset.mem_filter.mp hit).1⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm (Finset.mem_filter.mp last).2.1,(Finset.mem_filter.mp last).1⟩
  have h := Finset.card_le_card bound
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨nt,pt⟩),
    Finset.card_union_of_disjoint np,Finset.card_erase_of_mem hu] at h
  have pos := Finset.card_pos.mpr ⟨u,hu⟩
  change N.card+P.card+T.card+1≤_
  omega
open ThresholdFlowSum
/-- Nonnegativity of the physical row deficit, without signed subtraction. -/
theorem physical_degree_cap (u : Id C) (hu : u∈hubs C n)
    (two : ∀ x,(endpoints L x).card=2) (inj : Function.Injective (endpoints L))
    (noedge : ∀ a∈hubs C n,∀ b∈hubs C n,a≠b → active L a b=true →
      ∀ x : Fin n,a∈endpoints L x → b∉endpoints L x)
    (leaf : (singleAt L u).card≤1+max (fan L u) (leak L u))
    (fund : deltaO L+deltaA L+(hubs C n).card+2*n≤C.size+1) :
    (raws L u).card+(before L u).card+2*n ≤ C.size+3 := by
  classical
  let H := hubs C n
  have space := row_space L u hu noedge
  have dec := degrees_partition L u hu two inj
  have row := (probe_flow L u).trans (row_upper L u hu)
  have tally : (∑ i∈H,if u≠i ∧ active L u i=true then 1 else 0 : Nat)=(after L u).card := by
    simp [H,after,Finset.sum_boole]
  have split : (∑ i∈H.erase u,(fan L i-2))+(fan L u-2)=deltaO L :=
    Finset.sum_erase_add _ _ hu
  have fan2 : 2≤fan L u := by
    have mem : u∈ThresholdSharedOrBudget.sharedOrs C n := by simpa [hubs] using hu
    simpa [fan_readers] using (List.mem_filter.mp (List.mem_filter.mp mem).1).2
  change leak L u≤fan L u+_+_+_ at row
  rw [tally] at row
  change (∑ i∈H.erase u,(fan L i-2))+(fan L u-2)=deltaO L at split
  change leak L u≤fan L u+(after L u).card+(∑ i∈H.erase u,(fan L i-2))+deltaA L at row
  omega

/-- Hub incidence handshaking, including zero-raw hubs. -/
theorem sum_degrees (two : ∀ x,(endpoints L x).card=2) :
    (∑ u∈hubs C n,(raws L u).card)+(missed L).card=n+(internal L).card := by
  classical
  let H := hubs C n
  have rawSum : (∑ u∈H,(raws L u).card)=∑ x : Fin n,(hits L x).card := by
    simp only [raws,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    have same : H.filter (fun u => u∈endpoints L x)=hits L x := by
      ext u; simp [H,hits,and_comm]
    simpa only [Finset.sum_boole,Nat.cast_id] using congrArg Finset.card same
  have localEq (x : Fin n) : (hits L x).card+(if hits L x=∅ then 1 else 0 : Nat)=
      1+(if 2≤(hits L x).card then 1 else 0 : Nat) := by
    have cap : (hits L x).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans (two x).le
    by_cases empty : hits L x=∅
    · simp [empty]
    · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      by_cases hi : 2≤(hits L x).card <;> simp [empty,hi] <;> omega
  have sum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun x _ => localEq x)
  rw [rawSum]
  simpa [missed,internal,Finset.sum_add_distrib,Finset.sum_boole] using sum

theorem sum_before : (∑ u∈hubs C n,(before L u).card)=(hotPairs L).card := by
  classical
  simp only [before,hotPairs,Finset.card_filter,Finset.sum_product]
  rw [Finset.sum_comm]
#print axioms physical_degree_cap
#print axioms sum_degrees
end ThresholdHubDegrees
