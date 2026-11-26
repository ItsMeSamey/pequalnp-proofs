import ThresholdEndpointPorts
import ThresholdSharedPartition
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice ThresholdRegularSource ThresholdSimpleIncidence ThresholdSharedPartition
open ThresholdFanoutBudget T2OrPartition

/-- Physical geometry attached to a raw in singleAt. It records a normal
AND gate with ordered pins; no truth values or probe statements are inputs. -/
structure PrivateSite {C : Circuit} {n} (L : Layout C n) (u : Id C) (x : Fin n) where
  v : Id C
  z : Id C
  side : Bool
  other : Nat
  pair : endpoints L x={u,v}
  distinct : u≠v
  alone : readers C (n+v.val)=[z]
  consumer : (C.gates.get z).op=.and
  meet : Block.meet (n+z.val) (L.left z) (L.right z)∈forest L Fin.val
  pins : (if side then L.right z else L.left z)=n+v.val
  partner : (if side then L.left z else L.right z)=other
  separate : other≠n+v.val
  noOutput : C.output≠n+v.val
  group : ∃ p t, Block.group p t∈forest L Fin.val ∧ t.out=n+v.val

theorem private_site {C : Circuit} {n} (L : Layout C n) (M : LexMinimum n C)
    (u : Id C) (x : Fin n) (inS : x∈singleAt L u) (two : (endpoints L x).card=2) :
    Nonempty (PrivateSite L u x) := by
  classical
  have hitsU : hits L x={u} := (Finset.mem_filter.mp inS).2
  have umem : u∈endpoints L x := Finset.mem_of_mem_inter_left (show u∈hits L x by simp [hitsU])
  obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp two
  obtain ⟨v,uv,pair⟩ : ∃ v,u≠v ∧ endpoints L x={u,v} := by
    rw [eq] at umem
    rcases Finset.mem_insert.mp umem with same|other
    · subst a; exact ⟨b,ab,eq⟩
    · obtain rfl := Finset.mem_singleton.mp other
      exact ⟨a,Ne.symm ab,eq.trans (Finset.pair_comm _ _)⟩
  have ve : v∈endpoints L x := by simp [pair]
  have absent : v∉ThresholdSharedOrBudget.sharedOrs C n := by
    intro hit
    have hub : v∈hubs C n := by simpa [hubs] using hit
    have hv : v∈hits L x := Finset.mem_inter.mpr ⟨ve,hub⟩
    exact uv ((Finset.mem_singleton.mp (hitsU ▸ hv)).symm)
  obtain ⟨⟨z,side⟩,assigned,_⟩ := ThresholdFirstActive.unique_endpoint_pin M v ve absent
  have op : L.op z=.and := assigned.1
  have sq : (if side then L.right z else L.left z)=n+v.val := by
    cases side <;> exact assigned.2
  have lab : x.val∈labels L v := by simpa [endpoints] using ve
  unfold labels at lab
  split at lab
  next stop =>
    have vStop : T2OrPartition.next C n v=none := by simpa using stop
    have gm := mem_roots L Fin.val v vStop
    have vo := makeBlock_out L Fin.val v
    obtain ⟨p,t,bEq⟩ : ∃ p t,makeBlock L Fin.val v=Block.group p t := by
      cases e : makeBlock L Fin.val v with
      | meet j l r => simp [e,rawList] at lab
      | group p t => exact ⟨p,t,rfl⟩
    have isor : T2OrPartition.isOr C v=true := by
      apply (physical_op L v).mpr
      unfold makeBlock at bEq
      split at bEq <;> simp_all
    have cnt : (readers C (n+v.val)).length<2 := by
      by_contra! hi
      exact absent (by simp [ThresholdSharedOrBudget.sharedOrs,ThresholdSharedOrBudget.sharedGates,isor,hi])
    have rd : z∈readers C (n+v.val) := by
      apply read_mem
      rw [layout_inputs (L.atIndex z)]
      cases side <;> simp_all
    have pos := List.length_pos_of_mem rd
    obtain ⟨q,oq⟩ := List.length_eq_one_iff.mp (show (readers C (n+v.val)).length=1 by omega)
    have qz : z=q := List.mem_singleton.mp (oq ▸ rd)
    subst q
    have tag : (C.gates.get z).op=.and := by
      have lk := gate_lookup (L.atIndex z)
      have gl : C.gates.get z=binary (L.op z) (L.left z) (L.right z) := by simpa using lk
      rw [gl,op]; rfl
    have zStop : T2OrPartition.next C n z=none := by
      cases e : T2OrPartition.next C n z with
      | none => rfl
      | some j =>
        have o := (physical_op L z).mp (next_is_or e).1
        rw [op] at o; contradiction
    have meet := mem_roots L Fin.val z zStop
    have block : makeBlock L Fin.val z=.meet (n+z.val) (L.left z) (L.right z) := by
      unfold makeBlock; split <;> simp_all
    rw [block] at meet
    rw [bEq] at gm vo lab
    change t.out=n+v.val at vo
    change x.val∈t.raws at lab
    have noOut : C.output≠n+v.val := by
      intro same
      have lit := (ThresholdFirstActive.OrPath.raw (L:=L) (x:=x)).lit
      have shape := forest_checked L Fin.val _ gm
      have real := t.real shape (vector {x}) (by simp [vector])
      dsimp only at real
      have rawYes : t.raws.any (fun j => (C.wires (vector ({x} : Finset (Fin n)))).getD j false)=true := List.any_eq_true.mpr ⟨x.val,lab,lit⟩
      have accepted : C.eval (vector {x})=true := by
        change (C.wires _).getD C.output false=true
        rw [same,←vo,real,rawYes]; rfl
      have fail := (M.eligible.1 {x}).mp accepted
      simp at fail
    have distinctPins : L.left z≠L.right z := by
      have ct := ThresholdOrExtraction.singleton_port oq
      rw [layout_inputs (L.atIndex z)] at ct
      intro dup
      cases side <;> simp_all
    refine ⟨⟨v,z,side,_,pair,uv,oq,tag,meet,sq,rfl,?_,noOut,p,t,gm,vo⟩⟩
    cases side <;> simp_all <;> omega
  next => simp at lab
#print axioms private_site
end ThresholdStarBypass
