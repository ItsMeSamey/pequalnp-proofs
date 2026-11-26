import T2PhysicalMaximum
import Batteries.Tactic.OpenPrivate

namespace T2NamedProducer
open PEqualNP.CircuitLowerBounds ResidualSurplus T2PhysicalOverride T2PhysicalMaximum
open private read_earlier from GateSurplus

theorem split_row {α : Type} (gs : List α) (j : Nat) (hj : j < gs.length) :
    ∃ pre r post, gs = pre ++ r::post ∧ pre.length=j := by
  induction j generalizing gs with
  | zero =>
    cases gs with
    | nil => simp at hj
    | cons g gs => exact ⟨[],g,gs,rfl,rfl⟩
  | succ j ih =>
    cases gs with
    | nil => simp at hj
    | cons a gs =>
      obtain ⟨pre,r,post,eq,h⟩ := ih gs (by simpa using hj)
      exact ⟨a::pre,r,post,by simp [eq],by simp [h]⟩

theorem run_size (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [val g w])).length = _
    rw [ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem typed_split (gs : List Raw) (n p : Nat) (low : n≤p) (high : p<n+gs.length) :
    ∃ pre r post, gs=pre ++ r::post ∧ n+pre.length=p := by
  obtain ⟨a,r,b,h,len⟩ := split_row gs (p-n) (by omega)
  exact ⟨a,r,b,h,by omega⟩

theorem named_value (a b : List Raw) (r : Raw) (w : List Bool) :
    (run ((a ++ r::b).map native) w).getD (w.length + a.length) false = computed a r w := by
  let v := run (a.map native) w
  have len : v.length = w.length+a.length := by simp [v,run_size]
  have des : run ((a ++ r::b).map native) w =
      run (b.map native) (v ++ [val (native r) v]) := by simp [v,run,val,List.foldl_append]
  rw [des,←len, read_earlier _ _ _ (by simp)]
  exact getD_new v _

#print axioms named_value
end T2NamedProducer
