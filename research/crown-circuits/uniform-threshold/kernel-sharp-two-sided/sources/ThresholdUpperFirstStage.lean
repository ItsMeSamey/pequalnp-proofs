import ThresholdUpperBoxCount

namespace ThresholdUpperCatalogue
variable {V : Type*} [LinearOrder V]

theorem matching_spec (Q : Finset V) (d : V) (size : Q.card=4) (hd : d∈opposites Q) :
    (matching Q d).card=2 ∧ (matching Q d).biUnion id=Q ∧
    ∀ e∈matching Q d,∀ f∈matching Q d,e≠f → Disjoint e f := by
  classical
  have non : Q.Nonempty := Finset.card_pos.mp (by omega)
  let c := Q.min' non
  let P : Finset V := {c,d}
  let K := (Q.erase c).erase d
  have hc : c∈Q := Q.min'_mem non
  have dq : d∈Q.erase c := by simpa [opposites,non,c] using hd
  have pk : Disjoint P K := by
    apply Finset.disjoint_left.mpr
    intro x xp xk
    obtain ⟨xd,xk'⟩ := Finset.mem_erase.mp xk
    obtain ⟨xc,_⟩ := Finset.mem_erase.mp xk'
    rcases Finset.mem_insert.mp xp with h|h
    · exact xc h
    · exact xd (Finset.mem_singleton.mp h)
  have pn : P≠K := by
    intro eq
    have cp : c∈P := by simp [P]
    exact Finset.disjoint_left.mp pk cp (eq ▸ cp)
  have union : P∪K=Q := by
    ext x
    by_cases xc : x=c
    · subst x; simp [P,hc]
    by_cases xd : x=d
    · subst x; simp [P,(Finset.mem_erase.mp dq).2]
    simp [P,K,xc,xd]
  have m : matching Q d={P,K} := by simp [matching,anchor,non,P,K,c]
  rw [m]
  refine ⟨by simp [pn],by simpa using union,?_⟩
  intro e he f hf diff
  rcases Finset.mem_insert.mp he with rfl|heTail <;> rcases Finset.mem_insert.mp hf with rfl|hfTail
  · exact (diff rfl).elim
  · obtain rfl := Finset.mem_singleton.mp hfTail; exact pk
  · obtain rfl := Finset.mem_singleton.mp heTail; exact pk.symm
  · obtain rfl := Finset.mem_singleton.mp heTail
    obtain rfl := Finset.mem_singleton.mp hfTail
    exact (diff rfl).elim

structure FirstGraph (U : Finset V) (v k : Nat) where
  R : Finset (Finset V)
  ambient : R⊆edgeUniverse U
  edges : R.card=v
  degree : ∀ c∈U,(neighbors U R c).card<k
  F : Finset (Finset V)
  family : F=boxes U R
  four : F⊆U.powersetCard 4
  representative : ↥F ↪ ↥(R.powersetCard 2)
  endpoints : ∀ q,(representative q).val.biUnion id=q.val
  separated : ∀ q,∀ e∈(representative q).val,∀ f∈(representative q).val,e≠f → Disjoint e f

def sampleCount (w v : Nat) := (w.choose 2).choose v
def starCost (w v k : Nat) := (w*(w-1).choose k)*((w.choose 2)-k).choose (v-k)
def lossBudget (w v : Nat) := (w*(w-1).choose 2)*((w.choose 2)-2).choose (v-2)+
  (w.choose 4*3)*((w.choose 2)-4).choose (v-4)

theorem first_graph (U : Finset V) (v k : Nat) (four : 4≤v) (kf : k≤v)
    (room : starCost U.card v k<sampleCount U.card v) :
    ∃ G : FirstGraph U v k,
      v.choose 2 ≤ G.F.card + (lossBudget U.card v)/(sampleCount U.card v-starCost U.card v k) := by
  classical
  obtain ⟨R,mem,degree,budget⟩ := select U v k four kf room
  obtain ⟨sub,size⟩ := Finset.mem_powersetCard.mp mem
  let F := boxes U R
  have fourF : F⊆U.powersetCard 4 := Finset.filter_subset _ _
  let pick (q : ↥F) := (Finset.mem_filter.mp q.property).2.choose
  have picked (q : ↥F) : pick q∈liveNames R q.val := (Finset.mem_filter.mp q.property).2.choose_spec
  have op (q : ↥F) := (Finset.mem_filter.mp (picked q)).1
  have info (q : ↥F) := matching_spec q.val (pick q) (Finset.mem_powersetCard.mp (fourF q.property)).2 (op q)
  let repr (q : ↥F) : ↥(R.powersetCard 2) :=
    ⟨matching q.val (pick q),Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp (picked q)).2,(info q).1⟩⟩
  have inj : Function.Injective repr := by
    intro q r eq
    apply Subtype.ext
    exact (info q).2.1.symm.trans ((congrArg (fun a : ↥(R.powersetCard 2) => a.val.biUnion id) eq).trans (info r).2.1)
  let G : FirstGraph U v k := ⟨R,sub,size,degree,F,rfl,fourF,⟨repr,inj⟩,
    fun q => (info q).2.1,fun q => (info q).2.2⟩
  refine ⟨G,?_⟩
  have raw := box_count U R sub
  rw [size] at raw
  let lost := ((stars U 2).filter (fun s => star s⊆R)).card+
    ((cycles U).filter (fun s => cycle s⊆R)).card
  have paid : lost≤lossBudget U.card v/(sampleCount U.card v-starCost U.card v k) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<sampleCount U.card v-starCost U.card v k)).mpr
    simpa [lost,lossBudget,sampleCount,starCost,Nat.mul_comm] using budget
  change v.choose 2 ≤ F.card+_
  have cov : v.choose 2≤F.card+lost := by simpa [F,lost,Nat.add_assoc] using raw
  exact cov.trans (Nat.add_le_add_left paid _)

end ThresholdUpperCatalogue
