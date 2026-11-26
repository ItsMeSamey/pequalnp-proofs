import ThresholdSharedPairMinimum
import ThresholdSharedStructural
namespace ThresholdSharedPairMinimum
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdSharedPartition ThresholdSharedFlow T2OrPartition
private theorem group_of_endpoint {C : Circuit} {n} (L : Layout C n) (e : Fin n)
    (u : Id C) (hu : u∈endpoints L e) :
    ∃ p t, Block.group p t∈forest L Fin.val ∧ t.out=n+u.val ∧ e.val∈t.raws := by
  have lab : e.val∈labels L u := by simpa [endpoints] using hu
  unfold labels at lab
  split at lab
  next stop =>
    have mem : makeBlock L Fin.val u ∈ forest L Fin.val := by
      exact List.mem_map.mpr ⟨u,List.mem_filter.mpr ⟨List.mem_finRange _,stop⟩,rfl⟩
    have out := makeBlock_out L Fin.val u
    cases eq : makeBlock L Fin.val u with
    | meet i l r => simp [eq,rawList] at lab
    | group p t =>
      rw [eq] at lab mem out
      exact ⟨p,t,mem,out,lab⟩
  next => simp at lab

theorem regular_no_shared_raw {n out : Nat} {gs : List Raw}
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) (hn : 2≤n) :
    let L := layout n gs out M.eligible
    ∀ u∈hubs (source gs out) n, ∀ v∈hubs (source gs out) n, u≠v → active L u v=true →
      ∀ e : Fin n, u∈endpoints L e → v∉endpoints L e := by
  intro L u _ v _ ne on e eu ev
  obtain ⟨p,a,ua,ao,ax⟩ := group_of_endpoint L e u eu
  obtain ⟨q,b,wb,bo,bx⟩ := group_of_endpoint L e v ev
  exact regular_no_shared_edge M reg hn Fin.val u v ne p q a b ua wb ao bo on e.val ax bx
#print axioms regular_no_shared_raw
end ThresholdSharedPairMinimum
