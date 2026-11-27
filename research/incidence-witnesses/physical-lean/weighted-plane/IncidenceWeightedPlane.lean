import IncidencePinRunModel
import IncidencePinFreeSites
import IncidenceRunPinPhysical
namespace IncidenceWeightedPlane
open SparseIncidence IncidenceRobust IncidenceStartNormalization IncidencePinFreeSites
open IncidenceRunPinPhysical IncidencePinCompact
variable {n : Nat} (I : Fin n → Fin n → Prop) [DecidableRel I]
variable (C D : Circuit n) (P Q : Finset (Fin n)) (positive : 0<m P Q)

theorem small (pos : flags C I) (neg : negatives C I 2 2) (emptyP : P=∅)
    (removed : ∀ p∈P,∀ l,I p l → l∈Q)
    (lo : lower P Q ⁻¹' C.wire C.output ⊆ D.wire D.output)
    (hi : D.wire D.output ⊆ upper P Q ⁻¹' C.wire C.output)
    (A : Finset (Fin (m P Q))) (tiny : A.card≤2) :
    masks (raw P Q positive) A ∈ D.wire D.output ↔
      ∃ p l, I p l ∧ p∉P ∧ l∉Q ∧ key P Q positive (.inl p)∈A ∧ key P Q positive (.inr l)∈A := by
  let a : Input n := masks (raw P Q positive) A
  let u := upper P Q a
  have line (l) : u.2 l=true ↔ l∉Q ∧ key P Q positive (.inr l)∈A := by
    by_cases mem : l∈Q <;> simp [u,upper,mem,a,masks,right]
  have point (p) (h : p∉P) : u.1 p=true ↔ key P Q positive (.inl p)∈A := by
    simp [u,upper,h,a,masks,left]
  constructor
  · intro accepted
    by_contra none
    apply neg u.1 u.2 _ _ _ (hi accepted)
    · have free (p : Fin n) : p∉P := by simp [emptyP]
      let f : {p // u.1 p=true} → ↥A := fun p=>⟨_,(point p (free p)).1 p.property⟩
      have inj : Function.Injective f := by
        intro p r e
        have v := congrArg (fun t : ↥A=>tag P Q t.val) e
        change tag P Q (key P Q positive (.inl p.val))=tag P Q (key P Q positive (.inl r.val)) at v
        rw [tag_key _ _ _ ((left_free _ _ _).2 (free p)),
            tag_key _ _ _ ((left_free _ _ _).2 (free r))] at v
        exact Subtype.ext (Sum.inl.inj v)
      exact (Fintype.card_le_of_injective f inj).trans (by simpa using tiny)
    · let f : {l // u.2 l=true} → ↥A := fun l=>⟨_,((line l).1 l.property).2⟩
      have inj : Function.Injective f := by
        intro l k e
        have v := congrArg (fun t : ↥A=>tag P Q t.val) e
        change tag P Q (key P Q positive (.inr l.val))=tag P Q (key P Q positive (.inr k.val)) at v
        rw [tag_key _ _ _ ((right_free _ _ _).2 ((line l).1 l.property).1),
            tag_key _ _ _ ((right_free _ _ _).2 ((line k).1 k.property).1)] at v
        exact Subtype.ext (Sum.inr.inj v)
      exact (Fintype.card_le_of_injective f inj).trans (by simpa using tiny)
    · intro p l hp hl inc
      have pair := (line l).1 hl
      have free : p∉P := fun mem => pair.1 (removed p mem l inc)
      exact none ⟨p,l,inc,free,pair.1,(point p free).1 hp,pair.2⟩
  · rintro ⟨p,l,inc,fp,fl,mp,ml⟩
    apply lo
    apply IncidenceHoistSparse.wire_up C C.output C.output_lt _ (pos p l inc)
    constructor
    · intro q h
      have eq : q=p := by simpa [single] using h
      subst q; simpa [lower,fp,masks,left] using mp
    · intro q h
      have eq : q=l := by simpa [single] using h
      subst q; simpa [lower,fl,masks,right] using ml

theorem pair (pos : flags C I) (neg : negatives C I 2 2) (emptyP : P=∅)
    (removed : ∀ p∈P,∀ l,I p l → l∈Q)
    (lo : lower P Q ⁻¹' C.wire C.output ⊆ D.wire D.output)
    (hi : D.wire D.output ⊆ upper P Q ⁻¹' C.wire C.output)
    (x y : Fin (m P Q)) :
    masks (raw P Q positive) {x,y} ∈ D.wire D.output ↔ y∈neighbors I P Q x := by
  classical
  rw [small I C D P Q positive pos neg emptyP removed lo hi _ (Finset.card_le_two), neighbor_spec]
  constructor
  · rintro ⟨p,l,inc,hp,hl,a,b⟩
    have ep := tag_key P Q positive ((left_free P Q p).2 hp)
    have el := tag_key P Q positive ((right_free P Q l).2 hl)
    simp only [Finset.mem_insert,Finset.mem_singleton] at a b
    rcases a with a|a <;> rcases b with b|b <;> rw [a] at ep <;> rw [b] at el
    all_goals first | exact (by rw [ep,el]; exact inc) | exact (by rw [el,ep]; exact inc) |
      exact (by rw [ep] at el; contradiction)
  · intro edge
    have fx := tag_free P Q x
    have fy := tag_free P Q y
    have kx := key_tag P Q positive x
    have ky := key_tag P Q positive y
    cases xx : tag P Q x with
    | inl p =>
      cases yy : tag P Q y with
      | inl r => simp [xx,yy,Edge] at edge
      | inr l =>
        rw [xx] at fx kx; rw [yy] at fy ky
        exact ⟨p,l,by simpa [xx,yy,Edge] using edge,(left_free _ _ _).1 fx,
          (right_free _ _ _).1 fy,by simp [kx],by simp [ky]⟩
    | inr l =>
      cases yy : tag P Q y with
      | inr r => simp [xx,yy,Edge] at edge
      | inl p =>
        rw [xx] at fx kx; rw [yy] at fy ky
        exact ⟨p,l,by simpa [xx,yy,Edge] using edge,(left_free _ _ _).1 fy,
          (right_free _ _ _).1 fx,by simp [ky],by simp [kx]⟩

theorem singleton (pos : flags C I) (neg : negatives C I 2 2) (emptyP : P=∅)
    (removed : ∀ p∈P,∀ l,I p l → l∈Q)
    (lo : lower P Q ⁻¹' C.wire C.output ⊆ D.wire D.output)
    (hi : D.wire D.output ⊆ upper P Q ⁻¹' C.wire C.output)
    (x : Fin (m P Q)) : masks (raw P Q positive) {x} ∉D.wire D.output := by
  intro h
  have edge := (pair I C D P Q positive pos neg emptyP removed lo hi x x).1 (by simpa using h)
  rw [neighbor_spec] at edge
  cases e : tag P Q x <;> simp [e,Edge] at edge

theorem bound (bin : binary C) (pos : flags C I) (neg : negatives C I 2 2)
    (degree : ∀ l,Fintype.card {p // I p l}=402)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l) (hn : n=161203) : 643211≤C.size := by
  classical
  obtain ⟨D,sz,bD,liveD,out,_⟩ := IncidenceHoistPrune.prune C bin
  let E : Finset (Fin n) := ∅
  have count : m E E=322406 := by simp [total,E,hn]
  have hm : 0<m E E := by omega
  have lo : lower E E ⁻¹' C.wire C.output ⊆ D.wire D.output := by
    rw [out]; intro x h; simpa [lower,E] using h
  have hi : D.wire D.output ⊆ upper E E ⁻¹' C.wire C.output := by
    rw [out]; intro x h; simpa [upper,E] using h
  have rem (p : Fin n) (h : p∈E) (l : Fin n) (_ : I p l) : l∈E := by simp [E] at h
  have eq : IncidencePinPlaneGeometry.removedLines I E=E := by
    ext l; simp [IncidencePinPlaneGeometry.removed_iff,E]
  have deg : ∀ i : Fin (m E E),402≤(neighbors I E E i).card := by
    have h := min_degree I degree unique (by decide : 0<401) (by omega : n=401^2+401+1) E
    rw [eq] at h
    simpa [E] using h
  have r := IncidencePinRunModel.lower D (raw E E hm) bD liveD (neighbors I E E)
    (by decide : 1<402) deg (fun x y ne=>overlap I unique E E x y ne.symm)
    (singleton I C D E E hm pos neg rfl rem lo hi) (pair I C D E E hm pos neg rfl rem lo hi)
  rw [count] at r
  omega

#print axioms bound
end IncidenceWeightedPlane
