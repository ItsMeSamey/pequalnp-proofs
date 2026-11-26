import Research.PuncturedFanoRawGateCover
import Research.TrueOrCount
import PEqualNP.Defs.TopForm

/-! # OR and AND lower bounds for the punctured Fano incidence function

The circuit is constrained on the entire 14-bit Boolean cube. It must accept
every incidence using one of six mandatory columns, and may accept an input
only when it has an incidence in the full seven-column plane. A size at most
23 forces at least ten OR gates. With at most nine OR gates, at least sixteen
AND gates are necessary. The proof samples the eighteen mandatory edges
and nineteen maximal negatives and builds a marker trace of the actual
circuit on those inputs. -/

namespace FanoTrace
open PuncturedFanoMarkers
abbrev Sgn := Finset Nat
def sig (x : Nat) : Sgn := (Finset.range 37).filter (fun i => x.testBit i = true)
def neg (a : Sgn) : Sgn := a ∩ sig negativeMask
def pos (a : Sgn) : Sgn := a ∩ sig positiveMask
def initial : Set Sgn := {A | A = ∅ ∨ A = sig allMask ∨ ∃ r ∈ inputs, A = sig r}
inductive Run : Set Sgn → Set Sgn → Nat → Prop
  | start : Run initial ∅ 0
  | andGate {K O m x y} (prev : Run K O m) (hx : x ∈ K) (hy : y ∈ K) :
      Run (insert (x ∩ y) K) O (m+1)
  | orGate {K O m x y} (prev : Run K O m) (hx : x ∈ K) (hy : y ∈ K)
      (fresh : ∀ h ∈ O, Disjoint (neg (x ∪ y)) (neg h)) :
      Run (insert (x ∪ y) K) (insert (x ∪ y) O) m
theorem sig_and (a b : Nat) : sig (a &&& b) = sig a ∩ sig b := by
  ext i; simp [sig,Nat.testBit_and]; tauto
theorem sig_or (a b : Nat) : sig (a ||| b) = sig a ∪ sig b := by
  ext i; simp [sig,Nat.testBit_or]; tauto
@[simp] theorem sig_zero : sig 0 = ∅ := by ext; simp [sig]
end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers

def Legal (pool : Finset Nat) (A : Sgn) : Prop :=
  ∃ r ∈ rawConjunctions, ∃ hs : List Nat, (∀ h ∈ hs, h ∈ pool) ∧
    neg (sig r ∩ hs.foldr (fun h acc => sig h ∩ acc) (sig allMask)) = ∅ ∧
    A ⊆ pos (sig r ∩ hs.foldr (fun h acc => sig h ∩ acc) (sig allMask))

theorem legal_mono {pool pool' : Finset Nat} {A : Sgn} (h : pool ⊆ pool')
    (ha : Legal pool A) : Legal pool' A := by
  obtain ⟨r,hr,hs,hhs,hn,hp⟩ := ha
  exact ⟨r,hr,hs,fun x hx => h (hhs x hx),hn,hp⟩

end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers

private def markerFoldCheck : Bool := families.all fun f =>
  (products f).contains allMask && f.all fun a => (products f).all fun m =>
    (products f).contains (a &&& m)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
private theorem markerFold_checked : markerFoldCheck = true := by decide

private theorem markerFold_mem {f : List Nat} (hf : f ∈ families) (hs : List Nat)
    (hh : ∀ h ∈ hs, h ∈ f) : hs.foldr (fun h acc => h &&& acc) allMask ∈ products f := by
  have step := List.all_eq_true.mp markerFold_checked f hf
  simp only [Bool.and_eq_true,List.contains_iff_mem,List.all_eq_true] at step
  induction hs with
  | nil => exact step.1
  | cons x xs ih =>
    exact step.2 x (hh x (by simp)) _ (ih (fun h hx => hh h (by simp [hx])))

private theorem sig_fold (hs : List Nat) :
    sig (hs.foldr (fun h acc => h &&& acc) allMask) =
    hs.foldr (fun h acc => sig h ∩ acc) (sig allMask) := by
  induction hs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,sig_and,ih]

private theorem sig_positive_eq : sig positiveMask = Finset.range 18 := by decide

private theorem pos_sig_eq_edges (x : Nat) : pos (sig x) = edgeSet x := by
  unfold pos
  rw [sig_positive_eq]
  ext i
  simp only [Finset.mem_inter, sig, edgeSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, ht⟩, hi⟩
    exact ⟨hi, ht⟩
  · rintro ⟨hi, ht⟩
    exact ⟨⟨by omega, ht⟩, hi⟩

private theorem zero_of_neg_empty {x : Nat} (h : neg (sig x) = ∅) : x &&& negativeMask = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 37
  · have hem : i ∉ neg (sig x) := by simp [h]
    simp [neg,sig,hi] at hem
    cases hv : x.testBit i <;> simp [hv,hem]
  · have hn : negativeMask < 2^37 := by decide
    have hx : negativeMask.testBit i = false :=
      Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hx]

theorem legal_cover_bound {pool : Finset Nat} {paid : Finset Sgn}
    (hc : ∀ a ∈ pool, a ∈ candidates)
    (hd : ∀ a ∈ pool, ∀ b ∈ pool, a ≠ b → Disjoint (neg (sig a)) (neg (sig b)))
    (ha : ∀ A ∈ paid, Legal pool A)
    (hcover : sig positiveMask ⊆ paid.biUnion id) : 16 ≤ paid.card := by
  obtain ⟨f,hf,embed⟩ := admitted_marker_set pool hc (by
    intro a hpa b hpb hab
    have disj := hd a hpa b hpb hab
    apply beq_iff_eq.mpr
    apply zero_of_neg_empty
    rw [sig_and]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    simp only [neg, Finset.mem_inter] at hi
    exact Finset.disjoint_left.mp disj
      (Finset.mem_inter.mpr ⟨hi.1.1,hi.2⟩) (Finset.mem_inter.mpr ⟨hi.1.2,hi.2⟩))
  apply raw_gate_cover_bound f hf paid _ (sig_positive_eq ▸ hcover)
  intro A hA
  obtain ⟨r,hr,hs,hh,hn,hp⟩ := ha A hA
  refine ⟨r,hr,_,markerFold_mem hf hs (fun a h => embed a (hh a h)),?_,?_⟩
  · apply zero_of_neg_empty
    simpa only [sig_and,sig_fold] using hn
  · simpa only [← pos_sig_eq_edges,sig_and,sig_fold] using hp

end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers
abbrev Tag := Sgn × Option Nat
def factors (t : Option Tag) : List Nat := (t.bind Prod.snd).toList
def prodSig (ls : List Nat) := ls.foldr (fun h acc => sig h ∩ acc) (sig allMask)
def val (r : Nat) (t : Option Tag) := sig r ∩ prodSig (factors t)
def pool (T : Finset Tag) := T.biUnion fun k => k.2.toList.toFinset
def cover (P : Finset Sgn) := P.biUnion id

theorem sig_all : sig allMask = Finset.range 37 := by decide
theorem sig_sub_all (r : Nat) : sig r ⊆ sig allMask := by
  rw [sig_all]; exact Finset.filter_subset _ _
@[simp] theorem sig_inter_all (r : Nat) : sig r ∩ sig allMask = sig r :=
  Finset.inter_eq_left.mpr (sig_sub_all r)
@[simp] theorem val_none (r : Nat) : val r none = sig r := by simp [val,prodSig,factors]
@[simp] theorem val_unproductive (r : Nat) (A : Sgn) : val r (some (A,none)) = sig r := by
  simp [val,prodSig,factors]
@[simp] theorem val_productive (r c : Nat) (A : Sgn) : val r (some (A,some c)) = sig r ∩ sig c := by
  simp [val,prodSig,factors]
@[simp] theorem val_zero (t : Option Tag) : val 0 t = ∅ := by simp [val]
theorem prod_append (x y : List Nat) : prodSig (x++y) = prodSig x ∩ prodSig y := by
  have sub (z : List Nat) : prodSig z ⊆ sig allMask := by
    cases z with
    | nil => exact fun _ h => h
    | cons a as => exact Finset.inter_subset_left.trans (sig_sub_all a)
  induction x with
  | nil => exact (Finset.inter_eq_right.mpr (sub y)).symm
  | cons a as ih => change sig a ∩ prodSig (as++y) = (sig a ∩ prodSig as) ∩ prodSig y
                    rw [ih,Finset.inter_assoc]
theorem merge_val (r s : Nat) (t u : Option Tag) :
    val r t ∩ val s u = sig (r &&& s) ∩ prodSig (factors t ++ factors u) := by
  rw [sig_and,prod_append]
  ext; simp [val,and_assoc,and_left_comm,and_comm]
theorem raw_zero : 0 ∈ rawConjunctions := by decide
theorem raw_full : allMask ∈ rawConjunctions := by decide
theorem inputs_raw : ∀ r ∈ inputs, r ∈ rawConjunctions := by decide
set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem raw_and_mem : ∀ r ∈ rawConjunctions, ∀ s ∈ rawConjunctions, (r &&& s) ∈ rawConjunctions := by decide
set_option maxRecDepth 50000 in
theorem input_pair_candidate : ∀ a ∈ inputs, ∀ b ∈ inputs, a ≠ b → (a ||| b) ∈ candidates := by decide
set_option maxRecDepth 50000 in
theorem raw_live_pos : ∀ r ∈ rawConjunctions, (neg (sig r)).Nonempty →
    (pos (sig r)).Nonempty → r = allMask ∨ r ∈ inputs := by decide

inductive Mode (T : Finset Tag) (A : Sgn) (r : Nat) : Option Tag → Prop
  | bare (hn : neg A = neg (sig r)) : Mode T A r none
  | marked (k : Tag) (hk : k ∈ T) (live : (neg A).Nonempty) (sub : neg A ⊆ neg k.1) :
      Mode T A r (some k)
structure Describes (T : Finset Tag) (P : Finset Sgn) (A : Sgn) (r : Nat) (t : Option Tag) : Prop where
  raw_mem : r ∈ rawConjunctions
  mode : Mode T A r t
  below : val r t ⊆ A
  above : pos A ⊆ val r t ∪ cover P
  zero : neg A = ∅ → r=0

def Known (T : Finset Tag) (P : Finset Sgn) (A : Sgn) :=
  ∃ r t, Describes T P A r t

structure State (K O : Set Sgn) (m : Nat) where
  tags : Finset Tag
  paid : Finset Sgn
  count : paid.card ≤ m
  past : ∀ k ∈ tags, k.1 ∈ O
  sep : ∀ k ∈ tags, ∀ l ∈ tags, k ≠ l → Disjoint (neg k.1) (neg l.1)
  cand : ∀ k ∈ tags, ∀ c, k.2 = some c → c ∈ candidates ∧ sig c ⊆ k.1
  accounted : ∀ A ∈ paid, Legal (pool tags) A
  wires : ∀ A ∈ K, Known tags paid A

theorem cover_mono {P Q : Finset Sgn} (h : P ⊆ Q) : cover P ⊆ cover Q := by
  intro i hi
  obtain ⟨a,ha,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨a,h ha,hi⟩
theorem pool_mono {P Q : Finset Tag} (h : P ⊆ Q) : pool P ⊆ pool Q := by
  intro i hi
  obtain ⟨a,ha,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨a,h ha,hi⟩
theorem known_mono {T T' : Finset Tag} {P P' : Finset Sgn} {a : Sgn}
    (ht : T ⊆ T') (hp : P ⊆ P') (h : Known T P a) : Known T' P' a := by
  obtain ⟨r,t,d⟩ := h
  refine ⟨r,t,d.raw_mem,?_,d.below,d.above.trans (Finset.union_subset_union_right (cover_mono hp)),d.zero⟩
  cases d.mode with
  | bare hn => exact Mode.bare hn
  | marked k hk hl hs => exact Mode.marked k (ht hk) hl hs

end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers

theorem factors_pool {T : Finset Tag} {A : Sgn} {r : Nat} {t : Option Tag}
    (h : Mode T A r t) : ∀ m ∈ factors t, m ∈ pool T := by
  cases h with
  | bare => simp [factors]
  | marked k hk hl hs =>
    intro m hm
    apply Finset.mem_biUnion.mpr
    exact ⟨k,hk, List.mem_toFinset.mpr (by simpa [factors] using hm)⟩

theorem live_merge_mode {T : Finset Tag} {x y : Sgn} {r s : Nat} {t u : Option Tag}
    (sep : ∀ k ∈ T, ∀ l ∈ T, k ≠ l → Disjoint (neg k.1) (neg l.1))
    (hx : Mode T x r t) (hy : Mode T y s u) (live : (neg (x ∩ y)).Nonempty) :
    ∃ v : Option Tag, Mode T (x ∩ y) (r &&& s) v ∧
      val (r &&& s) v = val r t ∩ val s u := by
  have left : neg (x∩y) ⊆ neg x := fun _ hi => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1,(Finset.mem_inter.mp hi).2⟩
  have right : neg (x∩y) ⊆ neg y := fun _ hi => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).2,(Finset.mem_inter.mp hi).2⟩
  cases hx with
  | bare he =>
    cases hy with
    | bare he' =>
      have neg_inter (a b : Sgn) : neg (a∩b) = neg a ∩ neg b := by
        ext; simp [neg]
      refine ⟨none,Mode.bare (by rw [sig_and,neg_inter,neg_inter,he,he']),?_⟩
      simp [sig_and]
    | marked k hk hl hs =>
      refine ⟨some k,Mode.marked _ hk live (right.trans hs),?_⟩
      obtain ⟨a,_ | c⟩ := k <;> ext <;> simp [sig_and]
  | marked k hk hl hs =>
    cases hy with
    | bare =>
      refine ⟨some k,Mode.marked _ hk live (left.trans hs),?_⟩
      obtain ⟨a,_ | c⟩ := k
      · simp [sig_and]
      · ext i
        simp only [val_productive,val_none,sig_and,Finset.mem_inter]
        tauto
    | marked l hL hl' hs' =>
      have eq : k=l := by
        by_contra hn
        obtain ⟨i,hi⟩ := live
        exact Finset.disjoint_left.mp (sep _ hk _ hL hn) (hs (left hi)) (hs' (right hi))
      subst l
      refine ⟨some k,Mode.marked _ hk live (left.trans hs),?_⟩
      obtain ⟨a,_ | c⟩ := k
      · simp [sig_and]
      · ext i
        simp only [val_productive,sig_and,Finset.mem_inter]
        tauto

theorem and_state {K O : Set Sgn} {m : Nat} {x y : Sgn} (st : State K O m)
    (hx : x ∈ K) (hy : y ∈ K) : Nonempty (State (insert (x∩y) K) O (m+1)) := by
  classical
  obtain ⟨r,t,dx⟩ := st.wires x hx
  obtain ⟨s,u,dy⟩ := st.wires y hy
  let v := val r t ∩ val s u
  have below : v ⊆ x∩y := Finset.inter_subset_inter dx.below dy.below
  have above : pos (x∩y) ⊆ v ∪ cover st.paid := by
    intro i hi
    have hxx := dx.above (show i ∈ pos x from Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1,(Finset.mem_inter.mp hi).2⟩)
    have hyy := dy.above (show i ∈ pos y from Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).2,(Finset.mem_inter.mp hi).2⟩)
    dsimp [v]
    grind
  have raw := raw_and_mem r dx.raw_mem s dy.raw_mem
  by_cases hz : neg (x∩y) = ∅
  · let c := pos v
    let P := insert c st.paid
    have legal : Legal (pool st.tags) c := by
      refine ⟨r &&& s,raw,factors t ++ factors u,?_,?_,?_⟩
      · intro h hh
        rcases List.mem_append.mp hh with a|a
        · exact factors_pool dx.mode h a
        · exact factors_pool dy.mode h a
      · change neg (sig (r &&& s) ∩ prodSig (factors t ++ factors u)) = ∅
        rw [← merge_val]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hxy : i ∈ neg (x∩y) := Finset.mem_inter.mpr ⟨below (Finset.mem_inter.mp hi).1,(Finset.mem_inter.mp hi).2⟩
        simp [hz] at hxy
      · change pos v ⊆ pos (sig (r &&& s) ∩ prodSig (factors t ++ factors u))
        rw [← merge_val]
    have extend : st.paid ⊆ P := Finset.subset_insert ..
    refine ⟨⟨st.tags,P,(Finset.card_insert_le ..).trans (Nat.add_le_add_right st.count 1),
      st.past,st.sep,st.cand,?_,?_⟩⟩
    · intro A h
      rcases Finset.mem_insert.mp h with rfl|old
      · exact legal
      · exact st.accounted _ old
    · intro A hA
      rcases Set.mem_insert_iff.mp hA with rfl|old
      · refine ⟨0,none,raw_zero,Mode.bare (by rw [hz,sig_zero]; simp [neg]),by simp,?_,fun _ => rfl⟩
        simp only [val_zero,Finset.empty_union]
        intro i hi
        rcases Finset.mem_union.mp (above hi) with first|past
        · exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_insert_self ..,
            Finset.mem_inter.mpr ⟨first,(Finset.mem_inter.mp hi).2⟩⟩
        · exact cover_mono extend past
      · exact known_mono (fun _ h => h) extend (st.wires _ old)
  · obtain ⟨tag,md,eq⟩ := live_merge_mode st.sep dx.mode dy.mode (Finset.nonempty_iff_ne_empty.mpr hz)
    refine ⟨⟨st.tags,st.paid,by have := st.count; omega,st.past,st.sep,st.cand,st.accounted,?_⟩⟩
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl|old
    · exact ⟨_,_,raw,md,by rw [eq]; exact below,by rw [eq]; exact above,fun h => False.elim (hz h)⟩
    · exact st.wires _ old

end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers

private theorem or_parent {K O : Set Sgn} {m : Nat} {A B : Sgn} (st : State K O m)
    (ha : A ∈ K) (sub : A ⊆ B) (fresh : ∀ h ∈ O, Disjoint (neg B) (neg h)) :
    ∃ r, (r = 0 ∨ r = allMask ∨ r ∈ inputs) ∧ sig r ⊆ A ∧
      pos A ⊆ sig r ∪ cover st.paid ∧ (neg A = ∅ → r = 0) := by
  obtain ⟨r,t,d⟩ := st.wires A ha
  have modeFact := d.mode
  cases modeFact with
  | marked k hk live below =>
    obtain ⟨i,hi⟩ := live
    exact False.elim (Finset.disjoint_left.mp (fresh _ (st.past _ hk))
      (Finset.mem_inter.mpr ⟨sub (Finset.mem_inter.mp hi).1,(Finset.mem_inter.mp hi).2⟩)
      (below hi))
  | bare hn =>
    have hbelow : sig r ⊆ A := by simpa using d.below
    have habove : pos A ⊆ sig r ∪ cover st.paid := by simpa using d.above
    by_cases hp : (pos (sig r)).Nonempty
    · have hl : (neg (sig r)).Nonempty := by
        by_contra! he
        have zr := d.zero (hn.trans he)
        simp [zr,pos] at hp
      exact ⟨r,Or.inr (raw_live_pos _ d.raw_mem hl hp),hbelow,habove,d.zero⟩
    · refine ⟨0,Or.inl rfl,by simp,?_,fun _ => rfl⟩
      simp only [sig_zero,Finset.empty_union]
      intro i hi
      rcases Finset.mem_union.mp (habove hi) with h|h
      · exact False.elim (hp ⟨i,Finset.mem_inter.mpr ⟨h,(Finset.mem_inter.mp hi).2⟩⟩)
      · exact h

private theorem or_rep (r s : Nat)
    (hr : r = 0 ∨ r = allMask ∨ r ∈ inputs)
    (hs : s = 0 ∨ s = allMask ∨ s ∈ inputs) :
    ∃ a c, a ∈ rawConjunctions ∧ (∀ b, c = some b → b ∈ candidates ∧ sig b = sig r ∪ sig s) ∧
      ∀ z : Sgn, val a (some (z,c)) = sig r ∪ sig s := by
  have rr : r ∈ rawConjunctions := hr.elim (fun e => e ▸ raw_zero)
    (fun h => h.elim (fun e => e ▸ raw_full) (inputs_raw r))
  have ss : s ∈ rawConjunctions := hs.elim (fun e => e ▸ raw_zero)
    (fun h => h.elim (fun e => e ▸ raw_full) (inputs_raw s))
  rcases hr with rfl|rfl|hr
  · exact ⟨s,none,ss,by simp,by simp⟩
  · exact ⟨allMask,none,raw_full,by simp,by simp [Finset.union_eq_left.mpr (sig_sub_all s)]⟩
  rcases hs with rfl|rfl|hs
  · exact ⟨r,none,rr,by simp,by simp⟩
  · exact ⟨allMask,none,raw_full,by simp,by simp [Finset.union_eq_right.mpr (sig_sub_all r)]⟩
  by_cases he : r = s
  · subst s; exact ⟨r,none,rr,by simp,by simp⟩
  · refine ⟨allMask,some (r ||| s),raw_full,?_,?_⟩
    · intro b hb
      cases hb
      exact ⟨input_pair_candidate _ hr _ hs he,sig_or ..⟩
    · intro z
      rw [val_productive,Finset.inter_eq_right.mpr (sig_sub_all _),sig_or]

theorem or_state {K O : Set Sgn} {m : Nat} {x y : Sgn} (st : State K O m)
    (hx : x∈K) (hy : y∈K) (fresh : ∀h∈O, Disjoint (neg (x∪y)) (neg h)) :
    Nonempty (State (insert (x∪y) K) (insert (x∪y) O) m) := by
  classical
  let z := x ∪ y
  obtain ⟨r,hr,br,ar,zr⟩ := or_parent st hx (show x ⊆ z from Finset.subset_union_left) fresh
  obtain ⟨s,hs,bs,as',zs⟩ := or_parent st hy (show y ⊆ z from Finset.subset_union_right) fresh
  have below : sig r ∪ sig s ⊆ z := Finset.union_subset_union br bs
  have above : pos z ⊆ (sig r ∪ sig s) ∪ cover st.paid := by
    intro i hi
    have ⟨hxy,hp⟩ := Finset.mem_inter.mp hi
    rcases Finset.mem_union.mp hxy with h|h
    · have := ar (Finset.mem_inter.mpr ⟨h,hp⟩); grind
    · have := as' (Finset.mem_inter.mpr ⟨h,hp⟩); grind
  by_cases hz : neg z = ∅
  · have silent {w : Sgn} (hw : w ⊆ z) : neg w = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have h : i ∈ neg z := Finset.mem_inter.mpr ⟨hw (Finset.mem_inter.mp hi).1,(Finset.mem_inter.mp hi).2⟩
      simp [hz] at h
    have er := zr (silent Finset.subset_union_left)
    have es := zs (silent Finset.subset_union_right)
    refine ⟨⟨st.tags, st.paid, st.count, fun k hk => Set.mem_insert_of_mem _ (st.past k hk),
      st.sep,st.cand,st.accounted,?_⟩⟩
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl|h
    · refine ⟨0,none,raw_zero,Mode.bare (by change neg z = _; rw [hz]; simp [neg]),by simp,?_,fun _ => rfl⟩
      simpa [er,es] using above
    · exact st.wires _ h
  · obtain ⟨a,c,ha,hc,veq⟩ := or_rep r s hr hs
    let k : Tag := (z,c)
    let T := insert k st.tags
    have extT : st.tags ⊆ T := Finset.subset_insert ..
    have hk : k ∈ T := Finset.mem_insert_self ..
    refine ⟨⟨T,st.paid,st.count,?_,?_,?_,?_,?_⟩⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|old
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (st.past _ old)
    · intro j hj l hl hne
      rcases Finset.mem_insert.mp hj with rfl|hj <;> rcases Finset.mem_insert.mp hl with rfl|hl
      · exact False.elim (hne rfl)
      · exact fresh _ (st.past _ hl)
      · exact (fresh _ (st.past _ hj)).symm
      · exact st.sep _ hj _ hl hne
    · intro j hj b hb
      rcases Finset.mem_insert.mp hj with rfl|old
      · obtain ⟨hcan,he⟩ := hc b hb
        exact ⟨hcan,he ▸ below⟩
      · exact st.cand _ old _ hb
    · exact fun A hA => legal_mono (pool_mono extT) (st.accounted A hA)
    · intro A hA
      rcases Set.mem_insert_iff.mp hA with rfl|old
      · refine ⟨a,some k,ha,Mode.marked _ hk (Finset.nonempty_iff_ne_empty.mpr hz) (fun _ h => h),?_,?_,fun h => (hz h).elim⟩
        · simpa only [k,veq] using below
        · simpa only [k,veq] using above
      · exact known_mono extT (fun _ h => h) (st.wires _ old)

end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers

theorem initial_live : ∀ r ∈ inputs, (neg (sig r)).Nonempty := by decide
theorem all_live : (neg (sig allMask)).Nonempty := by decide
theorem start_state : Nonempty (State initial ∅ 0) := by
  classical
  refine ⟨⟨∅,∅,by simp,by simp,by simp,by simp,by simp,?_⟩⟩
  intro A h
  have bare (r : Nat) (hr : r ∈ rawConjunctions) (hz : neg (sig r) = ∅ → r=0) :
      Known ∅ ∅ (sig r) := by
    refine ⟨r,none,hr,Mode.bare rfl,by simp,?_,hz⟩
    simp only [val_none]
    exact Finset.inter_subset_left.trans Finset.subset_union_left
  rcases h with rfl|rfl|⟨r,hr,rfl⟩
  · simpa using bare 0 raw_zero (fun _ => rfl)
  · exact bare allMask raw_full (fun hz => False.elim (all_live.ne_empty hz))
  · exact bare r (inputs_raw _ hr) (fun hz => False.elim ((initial_live _ hr).ne_empty hz))

theorem sixteen_of_state {K O m} (st : State K O m) (out : sig positiveMask ∈ K) :
    16 ≤ m := by
  classical
  obtain ⟨r,t,dx⟩ := st.wires _ out
  have hz : neg (sig positiveMask) = ∅ := by decide
  have one : pos (sig positiveMask) = sig positiveMask := by simp [pos]
  have coverall := dx.above
  rw [dx.zero hz,val_zero,Finset.empty_union,one] at coverall
  apply (legal_cover_bound (pool := pool st.tags) (paid := st.paid) ?_ ?_ st.accounted coverall).trans st.count
  · intro i hi
    obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp hi
    exact (st.cand k hk i (by cases e : k.2 <;> simp_all)).1
  · intro a ha b hb ne
    obtain ⟨k,hk,ka⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨l,hl,lb⟩ := Finset.mem_biUnion.mp hb
    have ea : k.2 = some a := by cases e : k.2 <;> simp_all
    have eb : l.2 = some b := by cases e : l.2 <;> simp_all
    have diff : k ≠ l := by
      intro eq
      subst l
      rw [ea] at eb
      exact ne (Option.some.inj eb)
    have sa := (st.cand k hk a ea).2
    have sb := (st.cand l hl b eb).2
    exact (st.sep k hk l hl diff).mono (Finset.inter_subset_inter sa (fun _ h => h))
      (Finset.inter_subset_inter sb (fun _ h => h))
end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers
theorem run_state {K O m} (h : Run K O m) : Nonempty (State K O m) := by
  induction h with
  | start => exact start_state
  | andGate _ hx hy ih => exact ih.elim (fun st => and_state st hx hy)
  | orGate _ hx hy hf ih => exact ih.elim (fun st => or_state st hx hy hf)

theorem sixteen_ands_of_trace {K O m} (h : Run K O m) (out : sig positiveMask ∈ K) :
    16 ≤ m := (run_state h).elim fun st => sixteen_of_state st out
end FanoTrace

namespace PuncturedFanoMarkers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.MissingCell

/-- Physical wire 8 is the omitted column. -/
def fullFanoInput (b : Nat) : List Bool :=
  (List.range 14).map fun i => if i = 8 then false else b.testBit (if i < 8 then i else i-1)

def physicalWire (v : Nat) : Nat := if v < 8 then v else v+1

def goodFlips (b : Nat) : Finset Nat :=
  ((Finset.range 13).filter fun v => accepts (b ||| 2^v)).image physicalWire

theorem goodFlips_card : ∀ b ∈ negatives, (goodFlips b).card = 9 := by decide

theorem other_wires_preserved (b v k : Nat) (hk : k ≠ physicalWire v) :
    (fullFanoInput (b ||| 2^v)).getD k false = (fullFanoInput b).getD k false := by
  unfold fullFanoInput physicalWire at *
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < 14
  · rw [List.getElem?_eq_getElem (by simpa using h), List.getElem_range]
    simp only [Option.map_some, Option.getD_some]
    split <;> simp_all [Nat.testBit_or, Nat.testBit_two_pow]
    split_ifs at * <;> omega
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)]
    rfl

theorem eight_false_ors_of_flips (C : Circuit) (hm : Monotone2 C) (b : Nat) (hb : b ∈ negatives)
    (zero : C.eval (fullFanoInput b) = false)
    (on : ∀ v < 13, accepts (b ||| 2^v) = true → C.eval (fullFanoInput (b ||| 2^v)) = true) :
    8 ≤ falseOrCount C.gates (fullFanoInput b) := by
  have sub : goodFlips b ⊆ falseLive C.gates (fullFanoInput b) C.output := by
    intro j hj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
    by_contra absent
    have h := falseLive_semantic C (fullFanoInput b) (fullFanoInput (b ||| 2^v)) hm
      (by simp [fullFanoInput]) (fun k hk hzero => by
        rw [other_wires_preserved b v k (fun eq => absent (eq ▸ hk))]
        exact hzero) zero
    rw [on v (Finset.mem_range.mp hv) ha] at h
    contradiction
  have hc := Finset.card_le_card sub
  rw [goodFlips_card b hb] at hc
  have upper := falseLive_falseOrCount C.gates (fullFanoInput b) C.output (fun g hg => (hm g hg).2)
  omega

def fanoAssignment (b : Nat) (k : Fin 14) : Bool :=
  if k.val = 8 then false else b.testBit (if k.val < 8 then k.val else k.val-1)

theorem fano_as_list (b : Nat) : List.ofFn (fanoAssignment b) = fullFanoInput b := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, fullFanoInput, List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_ofFn, fullFanoInput, List.getElem_map, List.getElem_range, fanoAssignment]

def edgeAt (x : Fin 14 → Bool) (r c : Fin 7) : Prop :=
  (r = c ∨ r = c + 1 ∨ r = c + 3) ∧ x (Fin.castAdd 7 r) = true ∧ x (Fin.natAdd 7 c) = true

abbrev FanoBehavior (C : Circuit) : Prop := ∀ x : Fin 14 → Bool,
  (C.eval (List.ofFn x) = true → ∃ r c, edgeAt x r c) ∧
  ((∃ r c, c ≠ 1 ∧ edgeAt x r c) → C.eval (List.ofFn x) = true)

instance (x : Fin 14 → Bool) (r c : Fin 7) : Decidable (edgeAt x r c) := by
  unfold edgeAt
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem no_edge_on_negatives : ∀ b ∈ negatives, ¬ ∃ r c, edgeAt (fanoAssignment b) r c := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem edge_on_good_flips : ∀ b ∈ negatives, ∀ v : Fin 13, accepts (b ||| 2^v.val) = true →
    ∃ r c, c ≠ 1 ∧ edgeAt (fanoAssignment (b ||| 2^v.val)) r c := by decide

set_option maxHeartbeats 1000000 in
theorem edge_on_positives : ∀ b ∈ positives, ∃ r c, c ≠ 1 ∧ edgeAt (fanoAssignment b) r c := by decide

theorem fano_negative_eval (C : Circuit) (beh : FanoBehavior C) (b : Nat) (hb : b ∈ negatives) :
    C.eval (fullFanoInput b) = false := by
  cases he : C.eval (fullFanoInput b) with
  | false => rfl
  | true => exact False.elim (no_edge_on_negatives b hb ((beh (fanoAssignment b)).1 (by simpa only [fano_as_list] using he)))

theorem fano_positive_eval (C : Circuit) (beh : FanoBehavior C) (b : Nat) (hb : b ∈ positives) :
    C.eval (fullFanoInput b) = true := by
  simpa only [fano_as_list] using (beh _).2 (edge_on_positives b hb)

theorem fano_false_ors (C : Circuit) (hm : Monotone2 C) (beh : FanoBehavior C)
    (b : Nat) (hb : b ∈ negatives) : 8 ≤ falseOrCount C.gates (fullFanoInput b) := by
  apply eight_false_ors_of_flips C hm b hb (fano_negative_eval C beh b hb)
  intro v hv ha
  simpa only [fano_as_list] using (beh _).2 (edge_on_good_flips b hb ⟨v,hv⟩ ha)

theorem fano_or_bounds (C : Circuit) (hm : Monotone2 C) (beh : FanoBehavior C)
    (b : Nat) (hb : b ∈ negatives) (h : (C.gates.filter isOrGate).length ≤ 9) :
    8 ≤ (C.gates.filter isOrGate).length ∧ (trueOrFlags C.gates (fullFanoInput b)).count true ≤ 1 := by
  have := fano_false_ors C hm beh b hb
  have := trueOrFlags_balance C.gates (fullFanoInput b)
  omega

end PuncturedFanoMarkers

namespace FanoTrace
open PuncturedFanoMarkers PEqualNP.CircuitLowerBounds PEqualNP.Research.MissingCell

def proj (i : Nat) (w : List Sgn) := w.map (fun A => decide (i ∈ A))

theorem proj_read (i k : Nat) (w : List Sgn) :
    (proj i w).getD k false = decide (i ∈ w.getD k ∅) := by
  induction w generalizing k with
  | nil => simp [proj]
  | cons a w ih =>
    cases k with
    | zero => simp [proj]
    | succ k => simpa only [proj,List.map_cons,List.getD_cons_succ] using ih k

def sgate (g : Gate) (w : List Sgn) : Sgn :=
  let x := w.getD (g.inputs.getD 0 0) ∅
  let y := w.getD (g.inputs.getD 1 0) ∅
  if isOrGate g then x ∪ y else x ∩ y

def sstep (w : List Sgn) (g : Gate) := w ++ [sgate g w]

def Good (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b]

theorem good_gates (C : Circuit) (h : PEqualNP.TopForm.IsAO2 14 C) :
    ∀ g ∈ C.gates, Good g := by
  intro g hg
  refine ⟨h.1 g hg,?_⟩
  have hl := h.2.2 g hg
  rcases hinputs : g.inputs with _ | ⟨a, tail⟩
  · simp [hinputs] at hl
  rcases tail with _ | ⟨b, tail⟩
  · simp [hinputs] at hl
  rcases tail with _ | ⟨c,rest⟩
  · exact ⟨a,b,rfl⟩
  · simp [hinputs] at hl

theorem sgate_bit (g : Gate) (w : List Sgn) (i : Nat) (h : Good g) :
    decide (i ∈ sgate g w) = g.op.eval (g.inputs.map fun k => (proj i w).getD k false) := by
  obtain ⟨hop,a,b,hab⟩ := h
  simp_rw [proj_read]
  rcases hop with hop | hop <;> simp [sgate,hop,hab,isOrGate,GateOp.eval]

theorem proj_step (g : Gate) (w : List Sgn) (i : Nat) (h : Good g) :
    proj i (sstep w g) = advance g (proj i w) := by
  simpa only [proj,sstep,advance,List.map_append,List.map_cons,List.map_nil] using
    congrArg (fun b => proj i w ++ [b]) (sgate_bit g w i h)

theorem proj_fold (gs : List Gate) (w : List Sgn) (i : Nat) (good : ∀ g ∈ gs, Good g) :
    proj i (gs.foldl sstep w) = gs.foldl (fun v g => advance g v) (proj i w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun z hz => good z (List.mem_cons_of_mem _ hz)),proj_step _ _ _ (good _ (by simp))]

def ands (gs : List Gate) := (gs.filter (fun g => !isOrGate g)).length

theorem ands_balance (gs : List Gate) : ands gs + (gs.filter isOrGate).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : isOrGate g <;> simp [ands,h] at * <;> omega

private theorem read_in {K : Set Sgn} {w : List Sgn} (h : ∀ a ∈ w, a ∈ K)
    (z : (∅ : Sgn) ∈ K) (i : Nat) : w.getD i ∅ ∈ K := by
  induction w generalizing i with
  | nil => simpa using z
  | cons a ws ih =>
    cases i with
    | zero => simpa using h a (by simp)
    | succ i => simpa using ih (fun q hq => h q (by simp [hq])) i

private theorem run_trace_aux (gs : List Gate) (w : List Sgn) {K O : Set Sgn} {m : Nat}
    (prev : Run K O m) (allw : ∀ a ∈ w, a ∈ K) (zK : (∅ : Sgn) ∈ K)
    (good : ∀ g ∈ gs, Good g)
    (budget : ∀ i ∈ sig negativeMask, (trueOrFlags gs (proj i w)).count true ≤ 1)
    (blocked : ∀ h ∈ O, ∀ i ∈ neg h, true ∉ trueOrFlags gs (proj i w)) :
    ∃ K' O', Run K' O' (m + ands gs) ∧ ∀ k, (gs.foldl sstep w).getD k ∅ ∈ K' := by
  induction gs generalizing w K O m with
  | nil => exact ⟨K,O,prev,read_in allw zK⟩
  | cons g gs ih =>
    have hg := good g (by simp)
    obtain ⟨hop,a,b,hab⟩ := hg
    have good' := fun q hq => good q (List.mem_cons_of_mem g hq)
    have hp (i : Nat) := proj_step g w i ⟨hop,a,b,hab⟩
    have hflags (i : Nat) : trueOrFlags (g::gs) (proj i w) =
        (isOrGate g && decide (i ∈ sgate g w)) :: trueOrFlags gs (proj i (sstep w g)) := by
      simp only [trueOrFlags,hp,sgate_bit g w i ⟨hop,a,b,hab⟩]
    have budget' (i) (hi : i ∈ sig negativeMask) :
        (trueOrFlags gs (proj i (sstep w g))).count true ≤ 1 := by
      have H := budget i hi
      rw [hflags,List.count_cons] at H
      omega
    have blocked' (h) (hh : h ∈ O) (i) (hi : i ∈ neg h) :
        true ∉ trueOrFlags gs (proj i (sstep w g)) := by
      have H := blocked h hh i hi
      rw [hflags] at H
      exact fun bad => H (List.mem_cons_of_mem _ bad)
    have ha := read_in allw zK a
    have hb := read_in allw zK b
    have allw' : ∀ A ∈ sstep w g, A ∈ insert (sgate g w) K := by
      intro A hA
      rcases List.mem_append.mp hA with hA|hA
      · exact Set.mem_insert_of_mem _ (allw A hA)
      · simp only [List.mem_singleton] at hA
        exact hA ▸ Set.mem_insert _ _
    have zK' := Set.mem_insert_of_mem (sgate g w) zK
    rcases hop with hand|hor
    · have eqs : sgate g w = w.getD a ∅ ∩ w.getD b ∅ := by simp [sgate,hand,hab,isOrGate]
      have step : Run (insert (sgate g w) K) O (m+1) := eqs ▸ Run.andGate prev ha hb
      obtain ⟨K',O',H,Q⟩ := ih _ step allw' zK' good' budget' blocked'
      refine ⟨K',O',?_,Q⟩
      convert H using 1
      simp [ands,isOrGate,hand]
      omega
    · have eqs : sgate g w = w.getD a ∅ ∪ w.getD b ∅ := by simp [sgate,hor,hab,isOrGate]
      have fresh : ∀ h ∈ O, Disjoint (neg (sgate g w)) (neg h) := by
        intro h hh
        apply Finset.disjoint_left.mpr
        intro i hi hh'
        have H := blocked h hh i hh'
        rw [hflags] at H
        apply H
        have hmem := (Finset.mem_inter.mp hi).1
        simp [hor,isOrGate,hmem]
      have step : Run (insert (sgate g w) K) (insert (sgate g w) O) m := by
        rw [eqs] at fresh ⊢
        exact Run.orGate prev ha hb fresh
      have other : ∀ h ∈ insert (sgate g w) O, ∀ i ∈ neg h,
          true ∉ trueOrFlags gs (proj i (sstep w g)) := by
        intro h hh i hi
        rcases Set.mem_insert_iff.mp hh with rfl|hm
        · have ⟨mem,hn⟩ := Finset.mem_inter.mp hi
          have H := budget i hn
          simp [hflags,hor,isOrGate,mem] at H
          apply List.count_eq_zero.mp
          omega
        · exact blocked' h hm i hi
      obtain ⟨K',O',H,Q⟩ := ih _ step allw' zK' good' budget' other
      refine ⟨K',O',?_,Q⟩
      simpa [ands,List.filter_cons,hor,isOrGate] using H

def baseSigs : List Sgn :=
  (inputs.take 8).map sig ++ [∅] ++ (inputs.drop 8).map sig

def sample (i : Nat) := (positives ++ negatives).getD i 0

abbrev physicalInput := fullFanoInput

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
theorem base_projects : ∀ i : Fin 37, proj i.val baseSigs = physicalInput (sample i.val) := by
  decide

set_option maxRecDepth 4000 in
theorem classify_test : ∀ i : Fin 37,
    ((sample i.val ∈ positives ∧ i.val ∈ sig positiveMask) ∨
      (sample i.val ∈ negatives ∧ i.val ∉ sig positiveMask)) ∧
      (i.val ∈ sig negativeMask → sample i.val ∈ negatives) := by decide

theorem base_mem (A : Sgn) (h : A ∈ baseSigs) : A ∈ initial := by
  simp only [baseSigs,List.mem_append,List.mem_map,List.mem_singleton] at h
  rcases h with ((⟨r,hr,rfl⟩|rfl)|⟨r,hr,rfl⟩)
  · exact Or.inr (Or.inr ⟨r,List.mem_of_mem_take hr,rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨r,List.mem_of_mem_drop hr,rfl⟩)

theorem run_bounded {K O : Set Sgn} {m : Nat} (p : Run K O m) :
    ∀ A ∈ K, A ⊆ Finset.range 37 := by
  induction p with
  | start =>
    intro A h
    rcases h with rfl|rfl|⟨r,hr,rfl⟩
    · exact Finset.empty_subset _
    · exact Finset.filter_subset _ _
    · exact Finset.filter_subset _ _
  | andGate p hx hy ih =>
    intro A h
    rcases Set.mem_insert_iff.mp h with rfl|h
    · exact Finset.inter_subset_left.trans (ih _ hx)
    · exact ih _ h
  | orGate p hx hy fresh ih =>
    intro A h
    rcases Set.mem_insert_iff.mp h with rfl|h
    · exact Finset.union_subset (ih _ hx) (ih _ hy)
    · exact ih _ h

theorem circuit_run (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 14 C)
    (hpos : ∀ b ∈ positives, C.eval (physicalInput b) = true)
    (hneg : ∀ b ∈ negatives, C.eval (physicalInput b) = false)
    (hflags : ∀ b ∈ negatives, (trueOrFlags C.gates (physicalInput b)).count true ≤ 1) :
    ∃ K O, Run K O (C.size - (C.gates.filter isOrGate).length) ∧ sig positiveMask ∈ K := by
  have good := good_gates C ao
  have budget (i : Nat) (hi : i ∈ sig negativeMask) :
      (trueOrFlags C.gates (proj i baseSigs)).count true ≤ 1 := by
    have lt : i < 37 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    rw [base_projects ⟨i,lt⟩]
    exact hflags _ ((classify_test ⟨i,lt⟩).2 hi)
  obtain ⟨K,O,H,Q⟩ := run_trace_aux C.gates baseSigs Run.start base_mem (Or.inl rfl)
    good budget (by simp)
  let out := (C.gates.foldl sstep baseSigs).getD C.output ∅
  have mem : out ∈ K := Q C.output
  have eq : out = sig positiveMask := by
    ext i
    by_cases hi : i < 37
    · have e := proj_read i C.output (C.gates.foldl sstep baseSigs)
      rw [proj_fold _ _ _ good,base_projects ⟨i,hi⟩] at e
      change C.eval (physicalInput (sample i)) = decide (i ∈ out) at e
      rcases (classify_test ⟨i,hi⟩).1 with ⟨hp,hbit⟩|⟨hn,hbit⟩
      · rw [hpos _ hp] at e
        simp_all
      · rw [hneg _ hn] at e
        simp_all
    · have ho : i ∉ out := fun hm => hi (Finset.mem_range.mp (run_bounded H _ mem hm))
      simp [sig,hi,ho]
  refine ⟨K,O,?_,eq ▸ mem⟩
  have bal := ands_balance C.gates
  change Run K O (C.gates.length - _)
  convert H using 1
  omega

/-- On the nineteen critical negatives, at most nine OR gates make the
negative footprints of different true OR instructions disjoint. The run
therefore spends exactly one charge instruction for every AND in the circuit. -/
theorem circuit_run_of_behavior (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 14 C)
    (beh : FanoBehavior C) (h9 : (C.gates.filter isOrGate).length ≤ 9) :
    ∃ K O, Run K O (C.size - (C.gates.filter isOrGate).length) ∧ sig positiveMask ∈ K := by
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨ao.1 g hg, (ao.2.2 g hg).le⟩
  exact circuit_run C ao (fano_positive_eval C beh) (fano_negative_eval C beh)
    (fun b hb => (fano_or_bounds C hm beh b hb h9).2)

end FanoTrace

namespace FanoTrace
open PuncturedFanoMarkers PEqualNP.CircuitLowerBounds PEqualNP.Research.MissingCell
theorem punctured_fano_sixteen_ands (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 14 C)
    (beh : FanoBehavior C) (h9 : (C.gates.filter isOrGate).length ≤ 9) :
    16 ≤ C.size - (C.gates.filter isOrGate).length := by
  obtain ⟨K,O,tr,hw⟩ := circuit_run_of_behavior C ao beh h9
  exact sixteen_ands_of_trace tr hw

theorem punctured_fano_ten_ors (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 14 C)
    (beh : FanoBehavior C) (small : C.size ≤ 23) : 10 ≤ (C.gates.filter isOrGate).length := by
  by_contra! h
  have h9 : (C.gates.filter isOrGate).length ≤ 9 := by omega
  have hm : PEqualNP.MetaComplexity.Monotone2 C :=
    fun g hg => ⟨ao.1 g hg, (ao.2.2 g hg).le⟩
  have lower := (fano_or_bounds C hm beh 464 (by decide) h9).1
  have ands := punctured_fano_sixteen_ands C ao beh h9
  omega

example (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 14 C)
    (beh : FanoBehavior C) (bound : C.size ≤ 22) : 10 ≤ (C.gates.filter isOrGate).length :=
  punctured_fano_ten_ors C ao beh (by omega)
end FanoTrace
