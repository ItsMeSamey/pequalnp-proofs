import ThresholdStarEndpointRows
import ThresholdGraphCounts
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction T2SoleOrSplice
open ThresholdRegularSource ThresholdSimpleIncidence

/-- The selected group passes only its own star variable on singleton inputs;
simple incidence excludes every other incident raw from that private tree. -/
theorem alias_singleton_cold {C : Circuit} {n : Nat} (L : Layout C n)
    (u v : T2OrPartition.Id C) (uv : u≠v) (x z : Fin n) (xz : x≠z)
    (pair : endpoints L x={u,v}) (uz : u∈endpoints L z)
    (two : (endpoints L z).card=2) (inj : Function.Injective (endpoints L))
    (sel : Nat → Bool) (selected : sel (n+v.val)=true)
    (pre post : List Block) (p : Nat) (t : Tree)
    (split : forest L Fin.val=pre++ .group p t :: post) (root : t.out=n+v.val) :
    run (n+u.val) sel true (fun j => (vector {z}).getD j false)
      (forest L Fin.val) (fun _ => false) (n+v.val)=false := by
  have mem : Block.group p t∈forest L Fin.val := by rw [split]; simp
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp mem
  have wire := makeBlock_out L Fin.val i
  rw [eq] at wire
  change t.out=n+i.val at wire
  have iv : i=v := Fin.ext (by omega)
  subst i
  have zabs : z.val∉t.raws := by
    intro hit
    have stop : T2OrPartition.next C n v=none := by simpa using (List.mem_filter.mp hi).2
    have vz : v∈endpoints L z := by simpa [endpoints,labels,stop,eq,rawList] using hit
    have sub : ({u,v} : Finset (T2OrPartition.Id C))⊆endpoints L z := by
      intro w hw; rcases Finset.mem_insert.mp hw with same|other
      · simpa [same] using uz
      · simpa [Finset.mem_singleton.mp other] using vz
    have pairsame := Finset.eq_of_subset_of_card_le sub (by simp [two,uv])
    exact xz (inj (pair.trans pairsame))
  have rawOff : t.raws.any (fun j => (vector {z}).getD j false)=false := by
    cases h : t.raws.any (fun j => (vector {z}).getD j false) with
    | false => rfl
    | true =>
      obtain ⟨j,hj,on⟩ := List.any_eq_true.mp h
      rw [vec_get] at on
      split at on
      next small =>
        have jz : (⟨j,small⟩ : Fin n)=z := by simpa using on
        exact False.elim (zabs ((congrArg Fin.val jz) ▸ hj))
      next => contradiction
  have ord := forest_ordered L Fin.val
  rw [split,List.pairwise_append] at ord
  have later : ∀ b∈post,b.out≠n+v.val := by
    intro b hb
    have lt := (List.pairwise_cons.mp ord.2.1).1 b hb
    change t.out<b.out at lt
    omega
  have cat (front back : List Block) (f : Env) :
      run (n+u.val) sel true (fun j => (vector {z}).getD j false) (front++back) f =
      run (n+u.val) sel true (fun j => (vector {z}).getD j false) back
        (run (n+u.val) sel true (fun j => (vector {z}).getD j false) front f) := by
    induction front generalizing f with
    | nil => rfl
    | cons b fs ih => exact ih _
  have unchanged (xs : List Block) (f : Env) (away : ∀ b∈xs,b.out≠n+v.val) :
      run (n+u.val) sel true (fun j => (vector {z}).getD j false) xs f (n+v.val)=f (n+v.val) := by
    induction xs generalizing f with
    | nil => rfl
    | cons b bs ih =>
      change run _ _ _ _ bs _ _=_
      rw [ih _ (fun a ha => away a (by simp [ha]))]
      simp [put,Ne.symm (away b (by simp))]
  have apart : n+v.val≠n+u.val := by intro e; exact uv (Fin.ext (by omega))
  rw [split,cat]
  change run _ _ _ _ post _ _=_
  rw [unchanged post _ later]
  simp only [put,row,Block.out,root,apart,ite_false,ite_true,selected,rawOff]
  rfl

#print axioms alias_singleton_cold
end ThresholdStarBypass
