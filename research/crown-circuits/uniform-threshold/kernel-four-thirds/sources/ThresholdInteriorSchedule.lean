import ThresholdGraphPostorder
import ThresholdEdgeRows
namespace ThresholdPeelSchedule
open ThresholdGraphPostorder
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat} (j : V ↪ Fin m)
    (G : SimpleGraph V) (f : Pins m → Bool)

structure PathRows : Prop where
  single : ∀ {w z}, G.Adj w z → f {j w,j z}=false
  pair : ∀ {x w z}, x≠z → G.Adj x w → G.Adj w z → f (insert (j x) {j w,j z})=true

private theorem base_subset {base s : Finset V} {xs} (h : Peel G base s xs) : base ⊆ s := by
  induction h with
  | done => exact fun _ h => h
  | step fresh hw hz e d tail ih => exact ih.trans (Finset.subset_insert _ _)

theorem interior_schedule (rows : PathRows j G f) {base s : Finset V} {xs}
    (order : Peel G base s xs) (zpos : Pins m) (seed : zpos ⊆ base.map j) (pos : f zpos=true) :
    let ts := xs.map (fun x => Step.interior (j x))
    Scheduled f (s.map j) ts ∧ ending (s.map j) ts=base.map j := by
  induction order with
  | done => exact ⟨trivial,rfl⟩
  | @step s x w z xs fresh hw hz xw wz tail ih =>
    have hx : j x∉s.map j := by simpa using fresh
    have erase : (((insert x s).map j).erase (j x))=s.map j := by simp [fresh]
    have inc : s.map j ⊆ (insert x s).map j := Finset.map_subset_map.mpr (Finset.subset_insert _ _)
    have ws : j w∈s.map j := by simpa using hw
    have zs : j z∈s.map j := by simpa using hz
    have xz : x≠z := fun h => fresh (h ▸ hz)
    have xnot : j x∉({j w,j z} : Pins m) := by simp [xw.ne,xz]
    have small : ({j w,j z} : Pins m)⊆s.map j := Finset.insert_subset ws (Finset.singleton_subset_iff.mpr zs)
    have stay := seed.trans (Finset.map_subset_map.mpr (base_subset G tail))
    have newready : Ready f ((insert x s).map j) (.interior (j x)) := by
      refine ⟨{j w,j z},zpos,?_,stay.trans inc,xnot,fun hit => hx (stay hit),
        rows.single wz,rows.pair xz xw wz,pos⟩
      exact Finset.insert_subset (by simp) (small.trans inc)
    simpa only [List.map_cons,Scheduled,ending,after,erase] using
      And.intro (And.intro newready ih.1) ih.2
end ThresholdPeelSchedule
