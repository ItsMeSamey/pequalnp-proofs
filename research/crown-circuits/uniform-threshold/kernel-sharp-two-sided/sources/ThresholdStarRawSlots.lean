import ThresholdGraphCounts
import ThresholdLeakPins
import ThresholdFlowFanout
import Mathlib.Data.List.Nodup
namespace ThresholdStarRawSlots
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition ThresholdOrExtraction
open ThresholdOrGroups ThresholdSimpleIncidence ThresholdRegularSource ThresholdLeakPins
open ThresholdNamedIncidence T2SoleOrSplice
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def star (U : Id C) := Finset.univ.filter (fun x : Fin n => U ∈ endpoints L x)
def center (U : Id C) (p : Pin C) : Prop := n+p.1.val ∈ (makeBlock L Fin.val U).orIDs
noncomputable def choice {k : Nat} (U : Id C) (chosen : Fin n) (e : ↥(star L U) ≃ Fin k)
    (p : Pin C) : Bool ⊕ Fin k := by
  classical
  exact if h : source L p<n then
    let x : Fin n := ⟨source L p,h⟩
    if center L U p then .inl (decide (x=chosen)) else
    if hx : x∈star L U then .inr (e ⟨x,hx⟩) else .inl false
  else .inl false
noncomputable def input {k : Nat} (U : Id C) (chosen : Fin n) (e : ↥(star L U) ≃ Fin k)
    (v : Fin k → Bool) (p : Pin C) := (choice L U chosen e p).elim id v
noncomputable def fiber (x : Fin n) := Finset.univ.filter (fun p : Pin C => source L p=x.val)
noncomputable def centerFiber (U : Id C) (x : Fin n) : Finset (Pin C) := by
  classical
  exact (fiber L x).filter (center L U)

theorem input_center {k} (U : Id C) (chosen : Fin n) (e : ↥(star L U) ≃ Fin k)
    (v : Fin k → Bool) (p : Pin C) (h : source L p<n) (cen : center L U p) :
    input L U chosen e v p = decide (source L p = chosen.val) := by
  classical
  by_cases eq : source L p=chosen.val
  · have q : (⟨source L p,h⟩ : Fin n)=chosen := Fin.ext eq
    simp [input,choice,h,cen,eq,q]
  · have q : (⟨source L p,h⟩ : Fin n)≠chosen := fun h' => eq (congrArg Fin.val h')
    simp [input,choice,h,cen,eq,q]

theorem input_other {k} (U : Id C) (chosen : Fin n) (e : ↥(star L U) ≃ Fin k)
    (v : Fin k → Bool) (p : Pin C) (h : source L p<n) (cen : ¬ center L U p) :
    input L U chosen e v p = if hx : (⟨source L p,h⟩ : Fin n) ∈ star L U
      then v (e ⟨_,hx⟩) else false := by
  classical
  by_cases hx : (⟨source L p,h⟩ : Fin n) ∈ star L U <;> simp [input,choice,h,cen,hx]

theorem chosen_mem (U : Id C) (x : Fin n) (hx : x∈star L U) :
    x.val∈rawList (makeBlock L Fin.val U) := by
  classical
  have hh := (Finset.mem_filter.mp ((Finset.mem_filter.mp hx).2)).2
  change x.val∈labels L U at hh
  unfold labels at hh
  split at hh <;> simp_all

theorem all_fiber (x : Fin n) : (fiber L x).card = (readers C x.val).length := by
  classical
  change (Finset.univ.filter (fun p : Pin C => source L p=x.val)).card = _
  have count : (Finset.univ.filter (fun p : Pin C => source L p=x.val)).card =
      ∑ p : Pin C, if source L p=x.val then (1 : Nat) else 0 := by simp
  rw [count,Fintype.sum_prod_type]
  unfold readers
  rw [Fin.sum_univ_def,List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [Fintype.sum_bool,layout_inputs (L.atIndex i)]
  by_cases hl : L.left i=x.val <;> by_cases hr : L.right i=x.val <;> simp [source,hl,hr]

private theorem center_count (U : Id C) (x : Fin n) (stop : next C n U=none) :
    (centerFiber L U x).card = (rawList (makeBlock L Fin.val U)).count x.val := by
  classical
  let A := (makeBlock L Fin.val U).orIDs
  let S := Finset.univ.filter (fun i : Id C => n+i.val ∈ A)
  let wt := weight C n x.val
  have mb := mem_roots L Fin.val U stop
  have nd := (List.nodup_flatMap.mp (forest_nodup L Fin.val)).1 _ mb
  have rng (w : Nat) (hw : w∈A) : ∃ i : Id C, w=n+i.val :=
    forest_range L Fin.val w (List.mem_flatMap.mpr ⟨_,mb,hw⟩)
  have transfer : (∑ i ∈ S, wt (n+i.val)) = ∑ w ∈ A.toFinset, wt w := by
    apply Finset.sum_bij (fun i _ => n+i.val)
    · intro i hi; exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    · intro a _ b _ eq; exact Fin.ext (Nat.add_left_cancel eq)
    · intro w hw
      obtain ⟨i,rfl⟩ := rng w (List.mem_toFinset.mp hw)
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.mem_toFinset.mp hw⟩,rfl⟩
    · intros; rfl
  rw [block_count L x.isLt Fin.val U, ← List.sum_toFinset wt nd, ← transfer]
  let P := fun p : Pin C => source L p=x.val ∧ center L U p
  have ss : centerFiber L U x = Finset.univ.filter P := by ext; simp [centerFiber,fiber,P]
  have count : (Finset.univ.filter P).card =
      ∑ p : Pin C, if P p then (1 : Nat) else 0 := by simp
  rw [ss,count,Fintype.sum_prod_type]
  unfold S
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  have lk : C.gates[i.val]? = some (binary (L.op i) (L.left i) (L.right i)) := by
    simpa using (gate_lookup (L.atIndex i))
  have gl : C.gates[i.val].inputs = [L.left i,L.right i] := layout_inputs (L.atIndex i)
  by_cases ci : n+i.val ∈ A <;> by_cases hl : L.left i=x.val <;> by_cases hr : L.right i=x.val <;>
    simp [A] at ci <;>
    simp [P,center,A,source,wt,weight,ResidualSurplus.binary,List.count_cons,lk,ci,hl,hr,
      gl]

theorem center_once (U : Id C) (reg : MeetsInternal L) (hn : 2≤n) (M : LexMinimum n C)
    (stop : next C n U=none) (x : Fin n) :
    (centerFiber L U x).card = if x∈star L U then 1 else 0 := by
  classical
  rw [center_count L U x stop]
  have mem := mem_roots L Fin.val U stop
  cases h : makeBlock L Fin.val U with
  | meet => simp [star,endpoints,labels,stop,h,rawList]
  | group p t =>
    have nd := ThresholdUniqueRaw.group_raw_nodup L Fin.val reg hn M (h ▸ mem)
    simpa [star,endpoints,labels,stop,h,rawList] using (show t.raws.count x.val = _ from nd.count)

noncomputable def fixedPins {k : Nat} (U : Id C) (chosen : Fin n)
    (e : ↥(star L U) ≃ Fin k) := Finset.univ.filter (fun p : Pin C =>
      source L p<n ∧ (choice L U chosen e p).isLeft)

theorem fixed_card {k : Nat} (U : Id C) (chosen : Fin n) (e : ↥(star L U) ≃ Fin k)
    (reg : MeetsInternal L) (hn : 2≤n) (M : LexMinimum n C) (stop : next C n U=none)
    (two : ∀ x : Fin n, (readers C x.val).length=2) :
    (fixedPins L U chosen e).card = 2*n-k := by
  classical
  let F := fixedPins L U chosen e
  let name := fun p : Pin C => if h : source L p<n then (⟨source L p,h⟩ : Fin n) else chosen
  have pieces (x : Fin n) : F.filter (fun p => name p=x) =
      if x∈star L U then centerFiber L U x else fiber L x := by
    ext p
    by_cases h : source L p<n
    · let y : Fin n := ⟨source L p,h⟩
      by_cases yx : y=x
      · have nx : source L p=x.val := congrArg Fin.val yx
        by_cases st : x∈star L U <;> by_cases ce : center L U p <;>
          simp [F,fixedPins,choice,name,h,yx,nx,st,ce,centerFiber,fiber,y] at *
      · have nx : source L p≠x.val := fun z => yx (Fin.ext z)
        by_cases st : x∈star L U <;>
          simp [F,fixedPins,name,h,show (⟨source L p,h⟩ : Fin n)≠x from yx,st,centerFiber,fiber,nx]
    · have nx : source L p≠x.val := by intro z; rw [z] at h; exact h x.isLt
      by_cases st : x∈star L U <;> simp [F,fixedPins,name,h,st,centerFiber,fiber,nx]
  have counts (x : Fin n) : (F.filter (fun p => name p=x)).card +
      (if x∈star L U then 1 else 0) = 2 := by
    rw [pieces]
    by_cases st : x∈star L U
    · simp [st,center_once L U reg hn M stop]
    · simp [st,all_fiber,two]
  have total := Finset.sum_congr (s₁:=Finset.univ) rfl (fun x _ => counts x)
  have fibers : (∑ x : Fin n, (F.filter (fun p => name p=x)).card) = F.card := by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter F (Finset.univ : Finset (Fin n)) name)
  have kcard : (star L U).card=k := by simpa using Fintype.card_congr e
  rw [Finset.sum_add_distrib,fibers] at total
  have sumstar : (∑ x : Fin n, if x∈star L U then 1 else 0) = (star L U).card := by simp
  rw [sumstar,kcard] at total
  simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  have tot : F.card + k = n*2 := by simpa using total
  change F.card=2*n-k
  rw [Nat.mul_comm 2 n, ← tot, Nat.add_sub_cancel]

#print axioms fixed_card
end ThresholdStarRawSlots
