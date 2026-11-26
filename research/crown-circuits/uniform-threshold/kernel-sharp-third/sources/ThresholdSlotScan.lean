import ThresholdSlotBook
import ThresholdStarEndpointRows
namespace ThresholdSlotEvaluation
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition ThresholdStarRawSlots ThresholdStarBypass
open private any_congr from ThresholdStarBypassPhysical
variable {C : Circuit} {n : Nat} (L : Layout C n)

theorem readback (u : Nat) (raw V : Env) (bs : List Block) (seen : List Nat)
    (bk : Book C n seen bs)
    (rows : ∀ b∈bs,row u (fun _ => false) false raw V b=V b.out)
    (f : Env) (same : ∀ w∈seen,f w=V w) :
    ∀ w∈outputs bs seen,run u (fun _ => false) false raw bs f w=V w := by
  induction bs generalizing seen f with
  | nil => exact same
  | cons b bs ih =>
    obtain ⟨chk,refs,tail⟩ := bk
    have val := rows b (by simp)
    have congr : row u (fun _ => false) false raw f b =
        row u (fun _ => false) false raw V b := by
      cases b with
      | meet w x y =>
        have l := same x (refs x (by simp [Block.exts]))
        have r := same y (refs y (by simp [Block.exts]))
        simp [row,l,r]
      | group p t =>
        have eq := any_congr t.exts f V (fun w hw => same w (refs w hw))
        simp [row,eq]
    apply ih (b.out::seen) tail (fun a ha => rows a (by simp [ha]))
    intro j hj
    by_cases eq : j=b.out
    · subst j; simpa [put] using congr.trans val
    · simpa [put,eq] using same j ((List.mem_cons.mp hj).resolve_left eq)

theorem split_readback {k} (u : Id C) (x : Fin n) (hx : x∈star L u)
    (e : ↥(star L u) ≃ Fin k) (v : Fin k → Bool) (V : Nat → Bool)
    (T : Trace L (fun i b => input L u x e v (i,b)) V)
    (internal : MeetsInternal L) (stop : next C n u=none)
    (bk : Book C n [] (forest L Fin.val)) (w : Nat)
    (mem : w∈outputs (forest L Fin.val) []) :
    run (n+u.val) (fun _ => false) false (rawArm L u e v)
      (forest L Fin.val) (fun _ => false) w=V w := by
  apply readback _ _ _ _ [] bk _ _ (by simp) w mem
  intro b h
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  exact split_row L u x hx e v V T internal stop i hi

theorem center_hot {k} (u : Id C) (x : Fin n) (hx : x∈star L u)
    (e : ↥(star L u) ≃ Fin k) (v : Fin k → Bool) (V : Nat → Bool)
    (T : Trace L (fun i b => input L u x e v (i,b)) V)
    (internal : MeetsInternal L) (stop : next C n u=none) : V (n+u.val)=true := by
  have h := split_row L u x hx e v V T internal stop u (by simp [fixed,stop])
  simpa [row,makeBlock_out] using h.symm
end ThresholdSlotEvaluation
