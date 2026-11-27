import IncidenceResidualCut
import IncidenceResidualPorts
namespace IncidenceResidualPath
open CircuitRewire IncidenceResidualCut IncidenceResidualPorts
variable {m : ℕ} (C : Model m)

structure Graph (C : Model m) (k : ℕ) where
  N : Fin m→Finset (Fin m)
  degree : ∀ x,k≤(N x).card
  neg : ∀ x,({x}:Mask m)∉C.X C.out
  pos : ∀ x,∀ y∈N x,({x,y}:Mask m)∈C.X C.out
  dist : ∀ x r,r≠x → ∃ y∈N x,({r,y}:Mask m)∉C.X C.out

private def labels (u j : ℕ) (g : Gate) : List (ℕ×Bool) :=
  (if g.left=u then [(j,true)] else []) ++ (if g.right=u then [(j,false)] else [])
private def reads (u : ℕ) := (List.range C.s).flatMap fun j=>labels u j (C.g j)
private theorem count_labels (u j : ℕ) (g : Gate) : (labels u j g).length =
    (if g.left=u then 1 else 0)+(if g.right=u then 1 else 0) := by
  by_cases l : g.left=u <;> by_cases r : g.right=u <;> simp [labels,l,r]
private theorem count_reads (u : ℕ) : (reads C u).length+(if C.out=u then 1 else 0)=
    readers C.g C.s C.out u := by
  unfold reads readers
  congr 1
  generalize C.s=t
  induction t with
  | zero => simp
  | succ t ih => simp [List.range_succ,Finset.sum_range_succ,ih,count_labels]
private theorem labels_mem (u j t : ℕ) (g : Gate) (b : Bool) :
    (t,b)∈labels u j g ↔ t=j ∧ port g b=u := by
  by_cases l : g.left=u <;> by_cases r : g.right=u <;> cases b <;> simp [labels,port,l,r]
private theorem reads_mem (u t : ℕ) (b : Bool) :
    (t,b)∈reads C u ↔ t<C.s ∧ port (C.g t) b=u := by
  constructor
  · intro mem
    obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp mem
    obtain ⟨rfl,eq⟩ := (labels_mem ..).mp h
    exact ⟨List.mem_range.mp hj,eq⟩
  · rintro ⟨ht,h⟩
    exact List.mem_flatMap.mpr ⟨t,List.mem_range.mpr ht,(labels_mem ..).mpr ⟨rfl,h⟩⟩
theorem next_of_one (u : ℕ) (off : C.out≠u) (one : readers C.g C.s C.out u=1) :
    ∃ j b,Next C u j b := by
  have cnt := count_reads C u
  rw [if_neg off,Nat.add_zero,one] at cnt
  obtain ⟨⟨j,b⟩,only⟩ := List.length_eq_one_iff.mp cnt
  obtain ⟨js,read⟩ := (reads_mem C u j b).mp (by simp [only])
  refine ⟨j,b,js,read,?_⟩
  intro t ts d h
  have uniq := (reads_mem C u t d).mpr ⟨ts,h⟩
  simpa [only] using uniq

private theorem grow (x : Fin m) {v j b H} (p : Path C x v H) (q : Next C v j b)
    (op : (C.g j).op=.join) : Path C x (m+j) (insert (m+j) H) := by
  have later := port_early C j q.valid b
  rw [q.read] at later
  refine ⟨Finset.mem_insert_of_mem p.raw,Finset.mem_insert_self ..,?_,?_,?_⟩
  · intro i h; rcases Finset.mem_insert.mp h with rfl|h
    · exact le_rfl
    · exact (p.top i h).trans later.le
  · intro i h; rcases Finset.mem_insert.mp h with rfl|h
    · rw [C.law j q.valid]
      have on := p.hot _ p.last
      rw [← q.read] at on
      cases b <;> simp [port] at on <;> simp only [Gate.eval,op,Op.eval,Set.mem_union] <;> tauto
    · exact p.hot i h
  · intro t ht d hit
    rcases Finset.mem_insert.mp hit with h|h
    · exact Or.inl h
    · rcases p.boundary t ht d h with endWire|inside
      · have eq := (q.only t ht d endWire).1
        subst t
        exact Or.inr (Finset.mem_insert_self ..)
      · exact Or.inr (Finset.mem_insert_of_mem inside)

def End {k : ℕ} (G : Graph C k) (x : Fin m) (v : ℕ) : Prop :=
  v<m+C.s ∧ (∀ r : Fin m, ({r}:Mask m)∈C.X v ↔ r=x) ∧
    (2≤readers C.g C.s C.out v ∨ ∃ j b, Next C v j b ∧ (C.g j).op=.meet ∧
      ∀ y∈G.N x,({y}:Mask m)∈C.X (port (C.g j) (!b)))

theorem endpoint {k : ℕ} (G : Graph C k)
    (live : ∀ i<m+C.s,0<readers C.g C.s C.out i) (x : Fin m) :
    ∃ v,End C G x v := by
  classical
  have walk (fuel : ℕ) (v : ℕ) (H : Finset ℕ) (p : Path C x v H)
      (bound : v<m+C.s) (room : m+C.s≤max m (v+1)+fuel)
      (thin : ∀ r : Fin m,({r}:Mask m)∈C.X v ↔ r=x) : ∃ e,End C G x e := by
    induction fuel generalizing v H with
    | zero =>
      by_cases fork : 2≤readers C.g C.s C.out v
      · exact ⟨v,bound,thin,Or.inl fork⟩
      have nz := live v bound
      have out : C.out≠v := fun eq=>G.neg x (eq ▸ p.hot _ p.last)
      obtain ⟨j,b,q⟩ := next_of_one C v out (by omega)
      have later := port_early C j q.valid b
      rw [q.read] at later
      have js := q.valid
      omega
    | succ fuel ih =>
      by_cases fork : 2≤readers C.g C.s C.out v
      · exact ⟨v,bound,thin,Or.inl fork⟩
      have nz := live v bound
      have out : C.out≠v := fun eq=>G.neg x (eq ▸ p.hot _ p.last)
      obtain ⟨j,b,q⟩ := next_of_one C v out (by omega)
      have later := port_early C j q.valid b
      rw [q.read] at later
      have js := q.valid
      rcases C.bin j js with op|op
      · have cold (r : Fin m) (ne : r≠x) : ({r}:Mask m)∉C.X (port (C.g j) (!b)) := by
          obtain ⟨y,hy,zero⟩ := G.dist x r ne
          have edge := G.pos x y hy
          have plus : insert x ({r,y}:Mask m)∈C.X C.out :=
            mono C _ C.outBound (by intro i h; simp at h ⊢; tauto) edge
          have no := (erased C x p q _ (G.neg x) plus zero).1 op
          have early := port_early C j js (!b)
          exact fun h=>no (mono C _ (by omega) (by simp) h)
        have pg := grow C x p q op
        apply ih (m+j) _ pg (by omega) (by omega)
        intro r
        constructor
        · intro hit
          by_contra ne
          have no := cold r ne
          have skip : ({r}:Mask m)∉C.X (port (C.g j) b) := by rw [q.read]; exact fun h=>ne ((thin r).mp h)
          rw [C.law j js] at hit
          cases b <;> simp [port] at no skip <;> simp only [Gate.eval,op,Op.eval,Set.mem_union] at hit <;> tauto
        · rintro rfl; exact pg.hot _ pg.last
      · refine ⟨v,bound,thin,Or.inr ⟨j,b,q,op,?_⟩⟩
        intro y hy
        exact (erased C x p q {y} (G.neg x) (G.pos x y hy) (G.neg y)).2 op
  have initial : Path C x x.val {x.val} :=
    ⟨by simp,by simp,by simp,by simpa using (C.raw x {x}).2 (Finset.mem_singleton_self _),
      fun _ _ _ h=>Or.inl (Finset.mem_singleton.mp h)⟩
  apply walk C.s x.val _ initial (by omega) (by omega)
  intro r
  rw [C.raw]
  simp [eq_comm]

#print axioms endpoint
end IncidenceResidualPath
