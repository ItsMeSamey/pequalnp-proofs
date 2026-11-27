import IncidencePinCompact
import IncidenceResidualPair
namespace IncidencePinRunModel
open CircuitRewire SparseIncidence IncidenceStartNormalization IncidenceHoistPrune
open IncidenceResidualCut IncidenceResidualPorts IncidencePinCompact

def model {n m} (C : Circuit n) (raw : ℕ→Fin m) (bin : binary C) : Model m where
  s := C.size
  out := addr (n+n) m raw C.output
  g := gates C raw
  X := X C raw
  outBound := address_lt _ _ _ _ _ C.output_lt
  earlier := ordered C raw
  raw := fun i A=>by rw [raw_wire]; rfl
  law := law C raw
  bin := bin

theorem socket (g : ℕ→Gate) (s out i : ℕ)
    (h : i=out ∨ ∃ j<s,(g j).left=i ∨ (g j).right=i) : 0<readers g s out i := by
  rcases h with rfl|⟨j,hj,read⟩
  · simp [readers]
  · let f := fun j=>((if (g j).left=i then 1 else 0)+(if (g j).right=i then 1 else 0) : ℕ)
    have le : f j≤∑ t ∈ Finset.range s,f t :=
      Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr hj)
    have hot : 0<f j := by rcases read with eq|eq <;> simp [f,eq]
    change 0<(∑ t ∈ Finset.range s,f t)+_
    omega

/-- An accepted pair distinguished from its second singleton sensitizes the
first raw. Its physical fanout includes at least one actual socket. -/
theorem raw_live {m} (D : Model m) (x y : Fin m)
    (hit : ({x,y}:Mask m)∈D.X D.out) (off : ({y}:Mask m)∉D.X D.out) :
    0<readers D.g D.s D.out x.val := by
  by_contra! no
  have notOut : D.out≠x.val := fun e=>Nat.not_lt_of_ge no (socket _ _ _ _ (Or.inl e.symm))
  have sides (j : ℕ) (hj : j<D.s) : (D.g j).left≠x.val ∧ (D.g j).right≠x.val :=
    ⟨fun eq=>Nat.not_lt_of_ge no (socket _ _ _ _ (Or.inr ⟨j,hj,Or.inl eq⟩)),
     fun eq=>Nat.not_lt_of_ge no (socket _ _ _ _ (Or.inr ⟨j,hj,Or.inr eq⟩))⟩
  have same (i : ℕ) : i<m+D.s → i≠x.val →
      (({x,y}:Mask m)∈D.X i ↔ ({y}:Mask m)∈D.X i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro bound ne
      by_cases lo : i<m
      · let r : Fin m := ⟨i,lo⟩
        have rx : r≠x := fun e=>ne (congrArg Fin.val e)
        change ({x,y}:Mask m)∈D.X r.val ↔ ({y}:Mask m)∈D.X r.val
        rw [D.raw,D.raw]; simp [rx]
      let j:=i-m
      have e : i=m+j := by dsimp [j]; omega
      have js : j<D.s := by omega
      have ⟨hl,hr⟩ := D.earlier j js
      have l := ih (D.g j).left (by omega) (by omega) (sides j js).1
      have r := ih (D.g j).right (by omega) (by omega) (sides j js).2
      rw [e,D.law j js]
      rcases D.bin j js with op|op <;> simp only [Gate.eval,op,Op.eval,Set.mem_union,Set.mem_inter_iff] <;> tauto
  exact off ((same _ D.outBound notOut).mp hit)

theorem live_of_tests {n m} (C : Circuit n) (raw : ℕ→Fin m) (bin : binary C)
    (src : Live C) (neg : ∀ y : Fin m,masks raw {y}∉C.wire C.output)
    (hit : ∀ x : Fin m,∃ y : Fin m,masks raw {x,y}∈C.wire C.output) :
    let D := model C raw bin
    ∀ i<m+D.s,0<readers D.g D.s D.out i := by
  let D := model C raw bin
  have tr (A : Mask m) : A∈D.X D.out ↔ masks raw A∈C.wire C.output := by
    change A∈X C raw (addr (n+n) m raw C.output) ↔ _
    rw [output]; rfl
  change ∀ i<m+D.s,0<readers D.g D.s D.out i
  intro i bound
  by_cases lo : i<m
  · let x : Fin m := ⟨i,lo⟩
    obtain ⟨y,hy⟩ := hit x
    exact raw_live D x y ((tr _).mpr hy) (fun h=>neg y ((tr _).mp h))
  · let j:=i-m
    have e : i=m+j := by dsimp [j]; omega
    change i<m+C.size at bound
    have hj : j<C.size := by omega
    rw [e]
    exact socket _ _ _ _ (physical_gate_reader C raw src j hj)

theorem lower {n m k} (C : Circuit n) (raw : ℕ→Fin m) (bin : binary C)
    (src : Live C) (N : Fin m→Finset (Fin m)) (hk : 1<k) (deg : ∀ x,k≤(N x).card)
    (overlap : ∀ x r,r≠x → (N x∩N r).card≤1)
    (neg : ∀ y : Fin m,masks raw {y}∉C.wire C.output)
    (pairs : ∀ x y : Fin m,masks raw {x,y}∈C.wire C.output ↔ y∈N x) :
    2*m-1-(2*m)/(k+1)≤C.size := by
  let D := model C raw bin
  have tr (A : Mask m) : A∈D.X D.out ↔ masks raw A∈C.wire C.output := by
    change A∈X C raw (addr (n+n) m raw C.output) ↔ _
    rw [output]; rfl
  apply IncidenceResidualPair.lower D N hk deg overlap
  · exact fun x h=>neg x ((tr _).mp h)
  · exact fun x y=>(tr _).trans (pairs x y)
  · apply live_of_tests C raw bin src neg
    intro x
    have h := deg x
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0<(N x).card by omega)
    exact ⟨y,(pairs x y).2 hy⟩

#print axioms lower
end IncidencePinRunModel
