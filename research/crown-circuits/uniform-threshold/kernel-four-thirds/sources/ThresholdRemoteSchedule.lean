import ThresholdPeelSchedule
namespace ThresholdPeelSchedule
def names {m} (ps : List (Fin m × Fin m)) := ps.flatMap (fun p => [p.1,p.2])
def world {m} (center : Pins m) (ps : List (Fin m × Fin m)) :=
  center ∪ (names ps).toFinset

theorem remote_schedule {m} (f : Pins m → Bool) (center x z : Pins m)
    (xs : x⊆center) (zs : z⊆center) (fx : f x=false) (fz : f z=true)
    (ps : List (Fin m × Fin m)) (nd : (names ps).Nodup)
    (outside : ∀ i∈names ps, i∉center)
    (fp : ∀ p∈ps, f (insert p.2 (insert p.1 x))=true) :
    let ts := ps.map (fun p => Step.remote p.1 p.2)
    Scheduled f (world center ps) ts ∧ ending (world center ps) ts=center := by
  induction ps with
  | nil => simp [names,world,Scheduled,ending]
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    change (a::b::names ps).Nodup at nd
    have rest := (List.nodup_cons.mp (List.nodup_cons.mp nd).2)
    have ha := (List.nodup_cons.mp nd).1
    have uniq : a≠b ∧ a∉names ps := by simpa using ha
    have ac := outside a (by simp [names])
    have bc := outside b (by simp [names])
    have ih' := ih rest.2 (fun i hi => outside i (by change i∈a::b::names ps; simp [hi]))
      (fun p hp => fp p (by simp [hp]))
    have eq : world center ((a,b)::ps)=insert a (insert b (world center ps)) := by
      ext y; simp [world,names]
    have aw : a∉world center ps := by simp [world,uniq.2,ac]
    have bw : b∉world center ps := by simp [world,rest.1,bc]
    have erase : after (world center ((a,b)::ps)) (.remote a b)=world center ps := by
      simp [after,eq,aw,bw,uniq.1]
    have widen : center⊆world center ((a,b)::ps) := Finset.subset_union_left
    have aMem : a∈world center ((a,b)::ps) := by simp [eq]
    have bMem : b∈world center ((a,b)::ps) := by simp [eq]
    have ready : Ready f (world center ((a,b)::ps)) (.remote a b) :=
      ⟨uniq.1,x,z,Finset.insert_subset bMem (Finset.insert_subset aMem (xs.trans widen)),
        zs.trans widen,fun h => ac (xs h),fun h => bc (xs h),
        fun h => ac (zs h),fun h => bc (zs h),fx,fp (a,b) (by simp),fz⟩
    simpa only [List.map_cons,Scheduled,ending,erase] using And.intro (And.intro ready ih'.1) ih'.2
end ThresholdPeelSchedule
