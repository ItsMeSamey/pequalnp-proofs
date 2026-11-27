import IncidencePinFreeSites
import IncidenceRunPinPhysical
namespace IncidencePinRunTests
open SparseIncidence IncidenceRobust IncidenceStartNormalization IncidencePinFreeSites
open IncidenceRunPinPhysical IncidencePinCompact
variable {n : Nat} (I : Fin n → Fin n → Prop) [DecidableRel I]
variable (C D : Circuit n) (P Q : Finset (Fin n)) (positive : 0<m P Q)

theorem small (pos : flags C I) (neg : negatives C I n 2)
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
    · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun p=>u.1 p=true)
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

theorem pair (pos : flags C I) (neg : negatives C I n 2)
    (removed : ∀ p∈P,∀ l,I p l → l∈Q)
    (lo : lower P Q ⁻¹' C.wire C.output ⊆ D.wire D.output)
    (hi : D.wire D.output ⊆ upper P Q ⁻¹' C.wire C.output)
    (x y : Fin (m P Q)) :
    masks (raw P Q positive) {x,y} ∈ D.wire D.output ↔ y∈neighbors I P Q x := by
  classical
  rw [small I C D P Q positive pos neg removed lo hi _ (Finset.card_le_two), neighbor_spec]
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

theorem singleton (pos : flags C I) (neg : negatives C I n 2)
    (removed : ∀ p∈P,∀ l,I p l → l∈Q)
    (lo : lower P Q ⁻¹' C.wire C.output ⊆ D.wire D.output)
    (hi : D.wire D.output ⊆ upper P Q ⁻¹' C.wire C.output)
    (x : Fin (m P Q)) : masks (raw P Q positive) {x} ∉D.wire D.output := by
  intro h
  have edge := (pair I C D P Q positive pos neg removed lo hi x x).1 (by simpa using h)
  rw [neighbor_spec] at edge
  cases e : tag P Q x <;> simp [e,Edge] at edge

#print axioms pair
#print axioms singleton
end IncidencePinRunTests
