import ThresholdThreeLayerUpper
import Mathlib.Data.Finset.Sort
namespace ThresholdUpperNormalize
variable {A B : Type*} [LinearOrder A] [LinearOrder B]
noncomputable def label (S : Finset A) : Fin S.card ↪ A :=
  (S.orderIsoOfFin rfl).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
noncomputable def encode (S X : Finset A) := Finset.univ.filter (fun i => label S i∈X)
theorem label_mem (S : Finset A) (i) : label S i∈S := (S.orderIsoOfFin rfl i).property
theorem cover (S : Finset A) {a : A} (h : a∈S) : ∃ i,label S i=a := by
  let e := (S.orderIsoOfFin rfl).toEquiv
  exact ⟨e.symm ⟨a,h⟩,congrArg Subtype.val (e.apply_symm_apply ⟨a,h⟩)⟩
theorem mem_encode (S X : Finset A) (i) : i∈encode S X ↔ label S i∈X := by simp [encode]
theorem decode (S X : Finset A) (sub : X⊆S) : (encode S X).map (label S)=X := by
  ext a
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
    exact (mem_encode _ _ _).mp hi
  · intro h
    obtain ⟨i,eq⟩ := cover S (sub h)
    exact Finset.mem_map.mpr ⟨i,(mem_encode _ _ _).mpr (eq.symm ▸ h),eq⟩
theorem card_encode (S X : Finset A) (sub : X⊆S) : (encode S X).card=X.card := by
  simpa using congrArg Finset.card (decode S X sub)
theorem commute (S : Finset A) (T : Finset B) (X : Finset A) (next : A→Finset B)
    (sub : X⊆S) : (encode S X).biUnion (fun i => encode T (next (label S i))) =
      encode T (X.biUnion next) := by
  ext j
  constructor
  · intro h
    obtain ⟨i,hi,hj⟩ := Finset.mem_biUnion.mp h
    exact (mem_encode _ _ _).mpr (Finset.mem_biUnion.mpr
      ⟨_,(mem_encode _ _ _).mp hi,(mem_encode _ _ _).mp hj⟩)
  · intro h
    obtain ⟨a,ha,hj⟩ := Finset.mem_biUnion.mp ((mem_encode _ _ _).mp h)
    obtain ⟨i,eq⟩ := cover S (sub ha)
    exact Finset.mem_biUnion.mpr ⟨i,(mem_encode _ _ _).mpr (eq.symm ▸ ha),
      (mem_encode _ _ _).mpr (eq.symm ▸ hj)⟩

/-- Restrict each alphabet to symbols used starting from the n retained
labels. No ambient vertex or endpoint is charged if the n labels omit it. -/
theorem normalize {n v w z : Nat} (f : Fin n → Finset (Fin v))
    (g : Fin v → Finset (Fin w)) (k : Fin w → Finset (Fin z))
    (sf : ∀ i,(f i).card=2) (sg : ∀ i,(g i).card=2) (sk : ∀ i,(k i).card=2)
    (eight : ∀ i,((f i).biUnion (fun a => (g a).biUnion k)).card=8)
    (unique : Function.Injective (fun i => (f i).biUnion (fun a => (g a).biUnion k))) :
    ∃ v'≤v,∃ w'≤w,∃ z'≤z,Nonempty (ThresholdThreeLayerUpper.Layers n v' w' z') := by
  classical
  let S := Finset.univ.biUnion f
  let T := S.biUnion g
  let U := T.biUnion k
  let last := fun i => (f i).biUnion (fun a => (g a).biUnion k)
  have inS (i) : f i⊆S := fun _ h => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,h⟩
  have inT (a) (ha : a∈S) : g a⊆T := fun _ h => Finset.mem_biUnion.mpr ⟨a,ha,h⟩
  have inU (b) (hb : b∈T) : k b⊆U := fun _ h => Finset.mem_biUnion.mpr ⟨b,hb,h⟩
  have finalSub (i) : last i⊆U := by
    intro c hc
    obtain ⟨a,ha,hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨b,hb,hc⟩ := Finset.mem_biUnion.mp hc
    exact inU b (inT a (inS i ha) hb) hc
  let first := fun i => encode S (f i)
  let second := fun a => encode T (g (label S a))
  let third := fun b => encode U (k (label T b))
  have endeq (i) :
      (first i).biUnion (fun a => (second a).biUnion third)=encode U (last i) := by
    have step (a : Fin S.card) : (second a).biUnion third=encode U ((g (label S a)).biUnion k) :=
      commute T U _ k (inT _ (label_mem _ _))
    simp_rw [step]
    exact commute S U (f i) (fun a => (g a).biUnion k) (inS i)
  refine ⟨S.card,by simpa using Finset.card_le_univ S,T.card,by simpa using Finset.card_le_univ T,
    U.card,by simpa using Finset.card_le_univ U,⟨?_⟩⟩
  refine {first := first,second := second,third := third,
          firstTwo := fun i => (card_encode _ _ (inS i)).trans (sf i)
          secondTwo := fun a => (card_encode _ _ (inT _ (label_mem _ a))).trans (sg _)
          thirdTwo := fun b => (card_encode _ _ (inU _ (label_mem _ b))).trans (sk _)
          firstUsed := ?_,secondUsed := ?_,thirdUsed := ?_,eight := ?_,unique := ?_}
  · intro a
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (label_mem S a)
    exact ⟨i,(mem_encode _ _ _).mpr hi⟩
  · intro b
    obtain ⟨a,ha,hb⟩ := Finset.mem_biUnion.mp (label_mem T b)
    obtain ⟨i,eq⟩ := cover S ha
    exact ⟨i,(mem_encode _ _ _).mpr (eq.symm ▸ hb)⟩
  · intro c
    obtain ⟨b,hb,hc⟩ := Finset.mem_biUnion.mp (label_mem U c)
    obtain ⟨i,eq⟩ := cover T hb
    exact ⟨i,(mem_encode _ _ _).mpr (eq.symm ▸ hc)⟩
  · intro i
    rw [endeq,card_encode _ _ (finalSub i)]
    exact eight i
  · intro i j eq
    apply unique
    change last i=last j
    rw [←decode U _ (finalSub i),←decode U _ (finalSub j)]
    exact congrArg (Finset.map (label U)) ((endeq i).symm.trans (eq.trans (endeq j)))
end ThresholdUpperNormalize
