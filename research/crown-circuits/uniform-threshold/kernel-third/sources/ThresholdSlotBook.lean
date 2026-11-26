import ThresholdSlotTree
import ThresholdStarRawSlots
import ThresholdStarBypassPhysical
import Batteries.Tactic.OpenPrivate
namespace ThresholdSlotEvaluation
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition ThresholdStarRawSlots ThresholdLeakPins ThresholdStarBypass
open private distinct_parts from ThresholdSharedPairMinimum
open private any_congr from ThresholdStarBypassPhysical
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def rawArm {k} (u : Id C) (e : ↥(star L u) ≃ Fin k) (v : Fin k → Bool)
    (w : Nat) := if h : w<n then if hx : (⟨w,h⟩ : Fin n)∈star L u then v (e ⟨_,hx⟩) else false else false

theorem split_row {k} (u : Id C) (x : Fin n) (hx : x∈star L u)
    (e : ↥(star L u) ≃ Fin k) (v : Fin k → Bool) (V : Nat → Bool)
    (T : Trace L (fun i b => input L u x e v (i,b)) V)
    (internal : MeetsInternal L) (stop : next C n u=none) (i : Id C)
    (hi : i∈fixed C n) :
    let B := makeBlock L Fin.val i
    row (n+u.val) (fun _ => false) false (rawArm L u e v) V B=V B.out := by
  classical
  intro B
  let A := makeBlock L Fin.val u
  have fa : A∈forest L Fin.val := mem_roots L Fin.val u stop
  have fb : B∈forest L Fin.val := List.mem_map.mpr ⟨i,hi,rfl⟩
  have centerRaw := chosen_mem L u x hx
  have outB : B.out=n+i.val := makeBlock_out L Fin.val i
  have sep (ne : B≠A) (j : Id C) (hit : n+j.val∈B.orIDs) : ¬center L u (j,false) := by
    intro a
    have bad := distinct_parts _ B A ne fb fa _ hit a
    have mem : n+j.val∈allGates (forest L Fin.val) := List.mem_flatMap.mpr ⟨_,fb,hit⟩
    have good := List.nodup_iff_count_eq_one.mp (forest_nodup L Fin.val) _ mem
    omega
  have small (w : Nat) (hw : w∈B.exts) : n≤w := by
    obtain ⟨a,_,eq⟩ := (root_externals L internal Fin.val i w hw).1
    omega
  have cb : B.Checked C n := makeBlock_checked L Fin.val i
  cases hb : B with
  | meet w l r =>
    have neu : i≠u := by
      intro eq; subst i
      change x.val ∈ ThresholdRegularSource.rawList B at centerRaw
      simp [hb,ThresholdRegularSource.rawList] at centerRaw
    have h : w≠n+u.val := by rw [hb] at outB; change w=n+i.val at outB; intro a; apply neu; apply Fin.ext; omega
    have sides : L.op i=.and ∧ l=L.left i ∧ r=L.right i := by
      dsimp [B,makeBlock] at hb; split at hb <;> simp_all
    have sl := small l (by simp [hb,Block.exts])
    have sr := small r (by simp [hb,Block.exts])
    have rr := T.row i
    rw [hb] at outB
    change w=n+i.val at outB
    simpa [row,Block.out,h,←outB,sides.1,←sides.2.1,←sides.2.2,read,Nat.not_lt.mpr sl,Nat.not_lt.mpr sr,act] using rr.symm
  | group p t =>
    let raw := if i=u then fun w => decide (w=x.val) else rawArm L u e v
    have slots (j : Id C) (hit : n+j.val∈t.gates) (b : Bool)
        (h : source L (j,b)<n) : input L u x e v (j,b)=raw (source L (j,b)) := by
      have hit' : n+j.val∈B.orIDs := by simpa [hb,Block.orIDs] using hit
      by_cases same : i=u
      · have cen : center L u (j,b) := by simpa [center,←same,B] using hit'
        simpa [raw,same] using input_center L u x e v (j,b) h cen
      · have ne : B≠A := by
          intro eq
          have q := congrArg Block.out eq
          rw [outB,show A.out=n+u.val from makeBlock_out ..] at q
          exact same (Fin.ext (by omega))
        have neg : ¬center L u (j,b) := sep ne j hit'
        simpa [raw,same,rawArm,h] using input_other L u x e v (j,b) h neg
    have tt := tree_eq T raw t (by simpa [hb,Block.Checked] using cb)
      (fun w hw => small w (by simpa [hb,Block.exts] using hw))
      (fun j hj => ⟨by simpa [source] using slots j hj false,by simpa [source] using slots j hj true⟩)
    have shape : ∃ a l r,t=.join a l r := by
      dsimp [B,makeBlock] at hb; split at hb <;> simp_all [root]
      exact ⟨_,_,_,hb.2.symm⟩
    obtain ⟨w,l,r,rfl⟩ := shape
    change V w=_ at tt
    rw [hb] at outB
    change w=n+i.val at outB
    by_cases same : i=u
    · have mem : x.val∈(Tree.join w l r).raws := by
        change x.val∈ThresholdRegularSource.rawList (makeBlock L Fin.val u) at centerRaw
        simpa [←same,←show B=makeBlock L Fin.val i from rfl,hb,ThresholdRegularSource.rawList] using centerRaw
      have hot : (Tree.join w l r).raws.any raw=true := List.any_eq_true.mpr ⟨_,mem,by simp [raw,same]⟩
      rw [hot] at tt
      simpa [row,Block.out,Tree.out,outB,same] using tt.symm
    · have ne : w≠n+u.val := fun h => same (Fin.ext (by omega))
      simpa [row,Block.out,Tree.out,ne,raw,same] using tt.symm
end ThresholdSlotEvaluation
