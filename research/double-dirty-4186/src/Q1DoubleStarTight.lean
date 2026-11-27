import Q1DoubleStarGeometry
import Q1DoubleFourSlots
import Q1PrivateBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private OneLeak
variable {n k p r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {shared : Fin k → Clause n} {other : Fin p → Clause n}

theorem tight_external_batch (Y : Batch G C shared other 2) (four : NoFourCycle G)
    (slots : k+p=4) (many : 2≤k) (edge : Fin r → Bool → Fin n)
    (sound : ∀ i, G.Adj (edge i false) (edge i true))
    (sep : ∀ i j, i≠j → ∀ b c, edge i b ≠ edge j c)
    (hits : ∀ c i, edge i false ∈ shared c ∨ edge i true ∈ shared c)
    (exclusive : ∀ i j c, s(edge i false,edge i true) ≠ s(Y.pt j c,Y.pt j (!c))) :
    r≤1 := by
  classical
  let en : Fin 4 ≃ Fin k ⊕ Fin p := Fintype.equivOfCardEq (by simpa using slots.symm)
  let ix : Bool → Fin 2 := fun b => if b then 1 else 0
  let pt := fun i b => Y.pt (ix i) b
  let L := fun c => literals shared other (en c)
  have nz : ix false ≠ ix true := by decide
  have ixSep {a b : Bool} (h : a ≠ b) : ix a ≠ ix b := by
    cases a <;> cases b
    · exact (h rfl).elim
    · exact nz
    · exact Ne.symm nz
    · exact (h rfl).elim
  obtain ⟨f,patterns⟩ := tight_patterns four pt L (fun c i => Y.hits (en c) (ix i))
    (fun S h => Y.clean S (fun c => by simpa [L] using h (en.symm c)))
    (fun b c => Y.induced _ _ nz b c) (fun b c => Y.sep _ _ nz b c)
    (fun i => Y.edges (ix i)) (fun i => Y.res (ix i)) (fun c => Y.anchor (en c))
  let label (t : Pos) := pt t.1 t.2
  have inj : Function.Injective label := by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    have same : i=j := by
      by_contra ne
      exact Y.sep _ _ (ixSep ne) b c eq
    subst j
    have bc : b=c := by
      by_contra ne
      have ce : c=(!b) := by cases b <;> cases c <;> simp_all
      subst c
      exact G.ne_of_adj (Y.edges (ix i) b) eq
    subst c; rfl
  let pat (c : Fin k) : Pattern :=
    ((f (en.symm (.inl c))) false, (f (en.symm (.inl c))) true)
  have distinctP : Function.Injective pat := by
    intro c d eq
    have h : f (en.symm (.inl c)) = f (en.symm (.inl d)) := by
      funext b
      cases b
      · exact congrArg Prod.fst eq
      · exact congrArg Prod.snd eq
    exact Sum.inl.inj (en.symm.injective (f.injective h))
  let T := Finset.univ.image pat
  have convert (c : Fin k) {y} (h : y ∈ shared c) : inSlot label (pat c) y := by
    have hs : shared c = {pt false ((f (en.symm (.inl c))) false),
      pt true ((f (en.symm (.inl c))) true)} := by simpa [L,literals] using patterns (en.symm (.inl c))
    rw [hs] at h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl
    · exact ⟨(false,_),rfl,rfl⟩
    · exact ⟨(true,_),rfl,rfl⟩
  let fresh := fun a b => ∃ i, edge i false=a ∧ edge i true=b
  have alone : ∀ l m, ¬ fresh (label l) (label m) :=
    exclusive_external G label fresh (by rintro a b ⟨i,rfl,rfl⟩; exact sound i)
      (fun l m h => Y.induced _ _ (ixSep h) _ _)
      (by rintro i c ⟨j,a,b⟩; exact exclusive j (ix i) c (by rw [a,b]))
  let c : Fin k := ⟨0,by omega⟩
  let d : Fin k := ⟨1,by omega⟩
  have cd : c ≠ d := by intro h; have := congrArg Fin.val h; simp [c,d] at this
  apply tight_central_bound edge sep label inj T alone _ (Finset.mem_image_of_mem pat (Finset.mem_univ c))
    (Finset.mem_image_of_mem pat (Finset.mem_univ d)) (fun e => cd (distinctP e))
  intro i t ht
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  exact (hits j i).imp (convert j) (convert j)
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
