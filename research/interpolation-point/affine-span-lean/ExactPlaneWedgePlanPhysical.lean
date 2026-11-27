import ExactPlaneWedgePlan
import ExactPlaneWedgeCodecState
import ExactPlaneWedgeLeaf
import ExactPlanePhysicalWedgeTree
namespace ExactPlaneWedgePlanPhysical
open ExactPlaneWedgeProduct ExactPlaneWedgeArrayDP ExactPlaneWedgePlan ExactPlaneWedgeCodec
open ExactPlaneWedgeTree ExactPlanePhysicalWedgeTree ExactPlaneWedgeCodecState ExactPlaneWedgeSplit
variable {n d : Nat}
abbrev Tag := F × F
def physicalRows (k : Fin n→Word d) (b : Fin n→Tag) : LeafRows d n :=
  fun i c s => ExactPlaneWedgeLeaf.leaf i k b c.columns s
def boundary (k : Fin n→Word d) (t : Indexed d n) (E : Submodule F (Word d)) :=
  keySpan k (tree t) ⊓ E
def Represents (c : Cut d) (J : Submodule F (Word d)) : Prop :=
  ∃ e : Word c.rank ≃ₗ[F] J, ∀ x, image c.columns x=(e x).val
def Valid (k : Fin n→Word d) : (t : Indexed d n)→(E : Submodule F (Word d))→Prop
  | .leaf i c,E => Represents c (boundary k (.leaf i c) E)
  | .join l r c,E => Represents c (boundary k (.join l r c) E) ∧
    Valid k l (keySpan k (tree r)⊔E) ∧ Valid k r (keySpan k (tree l)⊔E)
theorem valid_here (k : Fin n→Word d) (t : Indexed d n) (E)
    (v : Valid k t E) : Represents (cut t) (boundary k t E) := by
  cases t with
  | leaf i c => exact v
  | join l r c => exact v.1
theorem exact (k : Fin n→Word d) (b : Fin n→Tag) (t : Indexed d n)
    (sep : separated (tree t)) (E : Submodule F (Word d)) (v : Valid k t E)
    (e : Word (cut t).rank ≃ₗ[F] boundary k t E)
    (he : ∀ x,image (cut t).columns x=(e x).val) (idx : Fin (size (cut t))) :
    semantics (plan (physicalRows k b) t) idx =
      family (leaves (tree t)) k b (decode e (stateVector (cut t))[idx]) := by
  induction t generalizing E with
  | leaf i c =>
    let code := (stateVector c)[idx]
    ext x
    exact ExactPlaneWedgeLeaf.leaf_exact i k b c.columns code (decode e code)
      (he _).symm (he _).symm (gamma_decode e code _) (gamma_decode e code _) x
  | join l r c il ir =>
    let L := keySpan k (tree l)
    let R := keySpan k (tree r)
    change Word c.rank ≃ₗ[F] ExactPlaneWedgeBoundary.parentBoundary L R E at e
    change Fin (size c) at idx
    let a := cut l
    let b' := cut r
    obtain ⟨ea,ha⟩ := valid_here k l (R⊔E) v.2.1
    obtain ⟨eb,hb⟩ := valid_here k r (L⊔E) v.2.2
    let va := stateVector a
    let vb := stateVector b'
    let s := (stateVector c)[idx]
    let ok := fun (i : Fin (size a)) (j : Fin (size b')) => compatible a.columns b'.columns c.columns va[i] vb[j] s
    have cmp (i : Fin (size a)) (j : Fin (size b')) :=
      compatible_decoded L R E a.columns b'.columns c.columns ea eb e ha hb he va[i] vb[j] s
    have eqL (i : Fin (size a)) := il sep.2.1 (R⊔E) v.2.1 ea ha i
    have eqR (j : Fin (size b')) := ir sep.2.2 (L⊔E) v.2.2 eb hb j
    ext x
    change x∈combine (fun i j=>ok i j=true) _ _ ↔ x∈family (leaves (tree l) ∪ leaves (tree r)) k b (decode e s)
    rw [mem_combine]
    apply Iff.trans _ (split_family (leaves (tree l)) (leaves (tree r)) sep.1 k b L R E
      (key_mem k (tree l)) (key_mem k (tree r)) (decode e s) x).symm
    constructor
    · rintro ⟨i,j,h,z,hz,w,hw,eq⟩
      exact ⟨_,_,(cmp i j).mp h,z,eqL i ▸ hz,w,eqR j ▸ hw,eq⟩
    · rintro ⟨sl,sr,h,z,hz,w,hw,eq⟩
      obtain ⟨ca,ra⟩ := decode_surjective ea sl
      obtain ⟨cb,rb⟩ := decode_surjective eb sr
      obtain ⟨i,ix⟩ := has_code a ca
      obtain ⟨j,jx⟩ := has_code b' cb
      have dl : decode ea va[i]=sl := (congrArg (decode ea) ix).trans ra
      have dr : decode eb vb[j]=sr := (congrArg (decode eb) jx).trans rb
      refine ⟨i,j,(cmp i j).mpr (dl ▸ dr ▸ h),z,?_,w,?_,eq⟩
      · rw [eqL i]; exact dl ▸ hz
      · rw [eqR j]; exact dr ▸ hw
#print axioms exact
end ExactPlaneWedgePlanPhysical
