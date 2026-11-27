import IncidenceCleanupLabels
import IncidenceSoleAndRetention
namespace IncidenceLiteralLabelStep
open CircuitRewire IncidenceZeroRestriction IncidenceSurvivingReads IncidenceSoleAndRetention
open IncidenceCleanupLabels IncidenceLabelHistory IncidenceForwardPins IncidenceLiteralPrefix
open scoped BigOperators

/-- Pin to zero without renumbering. Inactive original labels occupy no slots. -/
def retain (L : Finset ℕ) (x : ℕ) : Option ℕ := if x∈L then some x else none

theorem old_reads (m s : ℕ) (g : ℕ→Gate) (L : Finset ℕ) {x : ℕ} (hx : x∈L) (xm : x<m) :
    (starts m s g (retain L)).filter (fun p=>((retain L (readPin g p)).getD 0)=x) =
    (pins s).filter (fun p=>readPin g p=x) := by
  apply Finset.ext
  intro p
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hs,key⟩
    rcases Finset.mem_filter.mp hs with ⟨hp,_,live⟩
    by_cases good : readPin g p∈L
    · exact Finset.mem_filter.mpr ⟨hp,by simpa [retain,good] using key⟩
    · simp [retain,good] at live
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hp,ex⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp,ex ▸ xm,?_⟩,?_⟩ <;> simp [ex,retain,hx]

theorem old_and_kept {Z : Type*} (m s o : ℕ) (g : ℕ→Gate) (L L' : Finset ℕ)
    (domain : L'⊆Finset.range m) (X B : ℕ→Set Z)
    (ord : ∀k<s,OrderedBinary (g k) (m+k)) (sem : ∀k<s,X (m+k)=(g k).eval X)
    (base : ∀w<m,X w=read B (retain L' w)) (out : o<m+s)
    (flips : ∀x∈L',o≠x ∧ ∃a b : Z,(∀i<m,i≠x → (a∈X i ↔ b∈X i)) ∧ a∈X o ∧ b∉X o) :
    let p := compileLiteral m m g (retain L') s
    andLost (snap s g L) (snap p.size p.code L')=∅ := by
  classical
  let P := compileLiteral m m g (retain L') s
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨live,one,old,_after,no⟩ := Finset.mem_filter.mp hx
  change x∈L' at live
  obtain ⟨p,hp⟩ := of_decide_eq_true old
  obtain ⟨ps,reads,op⟩ := Finset.mem_filter.mp hp
  have jlt := (mem_pins p s).mp ps
  have xm := Finset.mem_range.mp (domain live)
  obtain ⟨different,a,b,agree,yes,low⟩ := flips x live
  let A := (pins s).filter (fun q=>readPin g q=x)
  have onlyPin {q : Pin} (qs : q∈pins s) (e : readPin g q=x) : q=p := by
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (show A.card=1 from one)
    have a : q∈A := Finset.mem_filter.mpr ⟨qs,e⟩
    have b : p∈A := Finset.mem_filter.mpr ⟨ps,reads⟩
    rw [ht,Finset.mem_singleton] at a b
    exact a.trans b.symm
  have unique (j : ℕ) (js : j<s) (diff : j≠p.1) : (g j).left≠x ∧ (g j).right≠x := by
    constructor
    · intro e; exact diff (congrArg Prod.fst (onlyPin ((mem_pins (j,false) s).mpr js) e))
    · intro e; exact diff (congrArg Prod.fst (onlyPin ((mem_pins (j,true) s).mpr js) e))
  have bound : ∀w<m,Below m (retain L' w) := by
    intro w hw v h; by_cases hl : w∈L' <;> simp [retain,hl] at h
    exact h ▸ hw
  obtain ⟨k,kt,kop,kread⟩ := IncidenceSoleAndRetention.physical m m s x p.1 o g (retain L') X B
    ord sem bound base jlt xm x (by simp [retain,live]) op p.2 reads unique out different a b agree yes low
  apply (of_decide_eq_false no)
  exact ⟨(k,p.2),Finset.mem_filter.mpr ⟨(mem_pins _ _).mpr kt,kread,kop⟩⟩

theorem step {Z : Type*} (m s o : ℕ) (g : ℕ→Gate) (L L' : Finset ℕ)
    (domain : L'⊆Finset.range m) (X B : ℕ→Set Z)
    (ord : ∀k<s,OrderedBinary (g k) (m+k)) (sem : ∀k<s,X (m+k)=(g k).eval X)
    (base : ∀w<m,X w=read B (retain L' w)) (out : o<m+s)
    (flips : ∀x∈L',o≠x ∧ ∃a b : Z,(∀i<m,i≠x → (a∈X i ↔ b∈X i)) ∧ a∈X o ∧ b∉X o)
    (z : ℕ→Bool) (rawDark : ∀w<m,(retain L' w).isNone=z w)
    (dense : ∀j<s,z (m+j)=deadOut (g j).op (z (g j).left) (z (g j).right))
    (liveCode : ∀j<s,j≠o-m → ∃q : Pin,j<q.1 ∧ q.1<s ∧ readPin g q=m+j)
    (internal : m≤o) (single : ℕ→Set ℕ)
    (input : ∀w<m,single w=read (fun x : ℕ=>({x} : Set ℕ)) (retain L' w))
    (gate : ∀j<s,single (m+j)=(g j).eval single) (reject : ∀x<m,x∉single o)
    (comp : Finset ℕ) (wide : ∀j∈comp,∃a b : ℕ,a≠b ∧
      a∈single (readPin g (j,z (g j).left)) ∧ b∈single (readPin g (j,z (g j).left))) :
    let P := compileLiteral m m g (retain L') s
    (drops (snap s g L) (snap P.size P.code L') ∪
      andLost (snap s g L) (snap P.size P.code L')).card≤(surplus s g z comp).card := by
  classical
  have stable := old_and_kept m s o g L L' domain X B ord sem base out flips
  let P := compileLiteral m m g (retain L') s
  let diff := fun x=>(((starts m s g (retain L')).filter
    (fun p=>(retain L' (readPin g p)).getD 0=x)).card -
    ((pins P.size).filter (fun p=>readPin P.code p=x)).card)
  have bound : ∀w<m,Below m (retain L' w) := by
    intro w hw v h; by_cases hl : w∈L' <;> simp [retain,hl] at h
    exact h ▸ hw
  have pay := IncidenceSurvivingReads.physical m m s (o-m) g (retain L') z ord rawDark dense
    bound liveCode single input gate (by simpa [Nat.add_sub_of_le internal] using reject) comp wide
  have pay' : ∑x∈Finset.range m,diff x ≤ (surplus s g z comp).card := pay
  change (drops (snap s g L) (snap P.size P.code L') ∪ andLost _ _).card≤_
  rw [stable,Finset.union_empty]
  apply (drops_le_debit _ _).trans
  apply le_trans _ pay'
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg domain (fun _ _ _=>Nat.zero_le _))
  apply Finset.sum_le_sum
  intro x hl
  change _ ≤ diff x
  simp only [diff,old_reads m s g L' hl (Finset.mem_range.mp (domain hl))]
  exact le_rfl
#print axioms step
end IncidenceLiteralLabelStep
