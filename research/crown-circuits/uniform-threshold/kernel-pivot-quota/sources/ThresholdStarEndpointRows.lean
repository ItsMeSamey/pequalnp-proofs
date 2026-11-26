import ThresholdStarBypassPhysical
import ThresholdStarMask
import ThresholdStarMonotone
import ThresholdSimpleIncidence
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource ThresholdSimpleIncidence
open private earlier from ThresholdOrGroups

theorem endpoint_hot {C : Circuit} {n : Nat} (L : Layout C n) (s : Finset (Fin n))
    (x : Fin n) (u : T2OrPartition.Id C) (xs : x∈s) (xu : u∈endpoints L x) :
    (C.wires (vector s)).getD (n+u.val) false=true := by
  have lab : x.val∈labels L u := by simpa [endpoints] using xu
  unfold labels at lab
  split at lab
  next stop =>
    have shape := makeBlock_checked L Fin.val u
    have out := makeBlock_out L Fin.val u
    cases e : makeBlock L Fin.val u with
    | meet j l r => simp [e,rawList] at lab
    | group p t =>
      rw [e] at lab shape out
      change x.val∈t.raws at lab
      change t.out=n+u.val at out
      have real := t.real shape (vector s) (by simp [vector])
      dsimp only at real
      rw [←out,real]
      have one : (C.wires (vector s)).getD x.val false=true := by
        change (ResidualSurplus.run C.gates _).getD _ false=_
        rw [earlier _ _ _ (by simpa [vector] using x.isLt),vec_get]
        simp [x.isLt,xs]
      have on : t.raws.any (fun j => (C.wires (vector s)).getD j false)=true :=
        List.any_eq_true.mpr ⟨x.val,lab,one⟩
      rw [on]; rfl
  next => simp at lab

theorem forced_nonempty_row {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (sel : Nat → Bool) (s : Finset (Fin n)) (x : Fin n)
    (u : T2OrPartition.Id (source gs out)) (xs : x∈s)
    (xu : u∈endpoints (layout n gs out M.eligible) x) :
    let L := layout n gs out M.eligible
    run (n+u.val) sel false (fun j => (vector s).getD j false)
      (forest L Fin.val) (fun _ => false) out=true ↔ 2≤s.card := by
  intro L
  rw [show run (n+u.val) sel false (fun j => (vector s).getD j false)
      (forest L Fin.val) (fun _ => false) out =
      (source gs out).eval (vector s) from regular_forced_hot M reg _ (by simp [vector]) _ sel
        (endpoint_hot L s x u xs xu)]
  exact M.eligible.1 s

/-- On the extracted forest, raw occurrences outside the named two roots are impossible. -/
theorem raw_free_off_pair {C : Circuit} {n : Nat} (L : Layout C n) (x : Fin n)
    (u v : T2OrPartition.Id C) (pair : endpoints L x ⊆ {u,v}) (b : Block)
    (mem : b∈forest L Fin.val) (notV : b.out≠n+v.val) : rawFree (n+u.val) x.val b := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
  by_cases eu : i=u
  · exact Or.inl (by simp [makeBlock_out,eu])
  apply Or.inr
  have stop : T2OrPartition.next C n i=none := by simpa using (List.mem_filter.mp hi).2
  have neither : i∉endpoints L x := by
    intro hit
    have pick := pair hit
    simp only [Finset.mem_insert,Finset.mem_singleton] at pick
    rcases pick with eq|eq
    · exact eu eq
    · exact notV (by simp [makeBlock_out,eq])
  have absent : x.val∉rawList (makeBlock L Fin.val i) := by
    simpa [endpoints,labels,stop] using neither
  cases e : makeBlock L Fin.val i with
  | meet => trivial
  | group p t => simpa [e,rawList] using absent

/-- For distinct star raws x,y the external arm of the private neighbor of x
is false on singleton y. Both rows are genuine raw assignments of the
original threshold circuit, and the unique-occurrence cut comes from endpoints. -/
theorem singleton_arm_off {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (sel : Nat → Bool) (x y : Fin n) (xy : x≠y)
    (u v : T2OrPartition.Id (source gs out))
    (uy : u∈endpoints (layout n gs out M.eligible) y)
    (pair : endpoints (layout n gs out M.eligible) x ⊆ {u,v})
    (pre post : List Block) (p : Nat) (t : Tree)
    (split : forest (layout n gs out M.eligible) Fin.val = pre ++ .group p t :: post)
    (root : t.out=n+v.val) :
    t.exts.any (run (n+u.val) sel false (fun j => (vector {y}).getD j false) pre
      (fun _ => false))=false := by
  let L := layout n gs out M.eligible
  have ordered := forest_ordered L Fin.val
  rw [split,List.pairwise_append] at ordered
  have before (b) (h : b∈pre) : rawFree (n+u.val) x.val b := by
    apply raw_free_off_pair L x u v pair b (by rw [split]; simp [h])
    have lt := ordered.2.2 b h (.group p t) (by simp)
    change b.out<t.out at lt
    omega
  have after (b) (h : b∈post) : rawFree (n+u.val) x.val b := by
    apply raw_free_off_pair L x u v pair b (by rw [split]; simp [h])
    have lt := (List.pairwise_cons.mp ordered.2.1).1 b h
    change t.out<b.out at lt
    omega
  apply clean_arm (n+u.val) x.val sel _ (fun j => (vector (insert x {y})).getD j false)
    (off_insert {y} x).2 pre post p t (fun _ => false) out before after
  have off := forced_nonempty_row M reg sel {y} y u (by simp) uy
  have on := forced_nonempty_row M reg sel (insert x {y}) y u (by simp) uy
  dsimp only at off on
  rw [split] at off on
  intro same
  have yes := on.mpr (by simp [xy])
  have bad := off.mp (same.trans yes)
  simp at bad

/-- The arm at the empty star is dominated by its value on another singleton.
Changing only its own raw cannot change the prefix before its group. -/
theorem empty_self_arm_off {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (sel : Nat → Bool) (x y : Fin n) (xy : x≠y)
    (u v : T2OrPartition.Id (source gs out)) (uy : u∈endpoints (layout n gs out M.eligible) y)
    (pair : endpoints (layout n gs out M.eligible) x ⊆ {u,v})
    (pre post : List Block) (p : Nat) (t : Tree)
    (split : forest (layout n gs out M.eligible) Fin.val = pre ++ .group p t :: post)
    (root : t.out=n+v.val) :
    let arm := fun (s : Finset (Fin n)) => t.exts.any (run (n+u.val) sel false
      (fun j => (vector s).getD j false) pre (fun _ => false))
    arm ∅=false ∧ arm {x}=false := by
  intro arm
  let src := fun (s : Finset (Fin n)) (j : Nat) => (vector s).getD j false
  have r : Below (src ∅) (src {y}) := by
    intro j
    change (vector (∅ : Finset (Fin n))).getD j false=true → _
    rw [vec_get]; split <;> simp
  have base : Below (fun _ => false) (fun _ => false) := fun _ h => h
  have dom := scan_monotone (n+u.val) sel false _ _ r pre _ _ base
  have low := singleton_arm_off M reg sel x y xy u v uy pair pre post p t split root
  have empty : arm ∅=false := by
    cases he : arm ∅ with
    | false => rfl
    | true =>
      obtain ⟨j,hj,on⟩ := List.any_eq_true.mp he
      have lit := List.any_eq_true.mpr ⟨j,hj,dom j on⟩
      rw [low] at lit
      contradiction
  have order := forest_ordered (layout n gs out M.eligible) Fin.val
  rw [split,List.pairwise_append] at order
  have free (b) (h : b∈pre) : rawFree (n+u.val) x.val b := by
    apply raw_free_off_pair _ x u v pair b (by rw [split]; simp [h])
    have lt := order.2.2 b h (.group p t) (by simp)
    change b.out<t.out at lt
    omega
  have mask := free_prefix (n+u.val) x.val sel (src ∅) pre (fun _ => false) free
  have rawEq : Away x.val (src ∅) (src {x}) := by
    simpa only [src,Away,Finset.insert_empty] using (off_insert (∅ : Finset (Fin n)) x).2
  have same := masked_eq _ _ _ _ _ rawEq _ _ mask
  have armsame : arm ∅=arm {x} := congrArg (fun f => t.exts.any f) same
  exact ⟨empty,armsame.symm.trans empty⟩

#print axioms empty_self_arm_off
#print axioms singleton_arm_off
#print axioms forced_nonempty_row
#print axioms raw_free_off_pair
end ThresholdStarBypass
