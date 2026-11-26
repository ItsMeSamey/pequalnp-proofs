import ThresholdWarmSimple
import ThresholdAlreadyHot
namespace ThresholdColumnConflicts
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence
open ThresholdEffectiveColumns ThresholdEffectiveSimplicity ThresholdPhysicalChangeEscape
open ThresholdWarmSimple ThresholdSharedFlow ThresholdStarBypass
open private different warm_fixed pivot from ThresholdWarmSimple

variable {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
  (reg : Regular n gs)
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
local notation "Cir" => source gs out
local notation "L" => layout n gs out M.eligible

private theorem transfer (x : Fin n) (u v : Id Cir) (hot : lit (C := Cir) x u)
    (probe : active L u v=true) : lit (C := Cir) x v :=
  ThresholdSharedPairErase.probe_le_actual L u (fun j => ((Cir).wires (vector {x})).getD j false)
    (fun i => ((L).atIndex i).eval (vector {x}) (by simp [vector])) hot _ probe

private theorem exposed (H : Finset (Id Cir)) (f a : Id Cir) (hf : f∈H)
    (ok : f∉exceptional L M H a) (x : Fin n) (e : endpoints L x={f,a})
    (w : Id Cir) (inc : w∈effective L M a) : lit (C := Cir) x w := by
  by_contra cold
  exact ok (Finset.mem_filter.mpr ⟨hf,x,e,w,inc,cold⟩)

include reg in
private theorem hide (f a b : Id Cir) (ab : a≠b) (fa : f≠a) (x y : Fin n)
    (old : endpoints L x={f,a}) (add : endpoints L y={f,b})
    (hot : lit (C := Cir) x b) : False := by
  apply ThresholdAlreadyHot.cannot_add M reg x y (different L ab fa old add)
  intro i hi
  rw [add] at hi
  rcases Finset.mem_insert.mp hi with rfl | eq
  · exact endpoint_hot L {x} x _ (by simp) (by simp [old])
  · obtain rfl := Finset.mem_singleton.mp eq
    exact hot

include reg in
theorem neighbors_bad (H : Finset (Id Cir)) (a w : Id Cir) (apart : a≠w)
    (inc : w∈effective L M a) :
    H.filter (fun f => Edge L f w) ⊆ missing L H a ∪ exceptional L M H a := by
  classical
  intro f hf
  obtain ⟨mem,_,y,add⟩ := Finset.mem_filter.mp hf
  by_contra bad
  have m : f∉missing L H a := fun h => bad (Finset.mem_union_left _ h)
  have c : f∉exceptional L M H a := fun h => bad (Finset.mem_union_right _ h)
  obtain ⟨fa,x,old⟩ : Edge L f a := by simpa [missing,mem] using m
  exact hide M reg f a w apart fa x y old add (exposed M H f a mem c x old w inc)

include reg in
theorem outgoing_conflict (H : Finset (Id Cir)) (a w b f : Id Cir)
    (apart : a≠b) (inc : w∈effective L M a) (mem : f∈H)
    (warm : f∉exceptional L M H a) (af : Edge L f a) (bf : Edge L f b) :
    active L w b≠true := by
  intro trip
  obtain ⟨fa,x,old⟩ := af
  obtain ⟨_,y,add⟩ := bf
  exact hide M reg f a b apart fa x y old add
    (transfer M x w b (exposed M H f a mem warm x old w inc) trip)

include reg in
theorem incoming_bad (H : Finset (Id Cir)) (a c w v : Id Cir)
    (apart : a≠c) (cv : effective L M c={w,v}) (av : v∈effective L M a) :
    H.filter (fun b => active L b w=true) ⊆
      (missing L H a ∪ missing L H c) ∪ exceptional L M H a := by
  classical
  intro b h
  obtain ⟨hb,probe⟩ := Finset.mem_filter.mp h
  by_contra fail
  have notA : b∉missing L H a := fun bad => fail (by simp [bad])
  have notC : b∉missing L H c := fun bad => fail (by simp [bad])
  have warm : b∉exceptional L M H a := fun bad => fail (by simp [bad])
  obtain ⟨ba,x,old⟩ : Edge L b a := by simpa [missing,hb] using notA
  obtain ⟨bc,y,add⟩ : Edge L b c := by simpa [missing,hb] using notC
  have litB := endpoint_hot L {x} x b (by simp) (by simp [old])
  have litW := transfer M x b w litB probe
  have litV := exposed M H b a hb warm x old v av
  obtain ⟨q,p,ps,edge,rest,mark,path⟩ := native_escape M reg x y
    (different L apart ba old add) b c bc (by simp [old]) add
  apply exclude_change L M edge rest mark path
  intro z hz
  rw [cv] at hz
  rcases Finset.mem_insert.mp hz with rfl|eq
  · exact warm_fixed M x y _ litW
  · obtain rfl := Finset.mem_singleton.mp eq
    exact warm_fixed M x y _ litV

private theorem walk_le {i q : Id Cir} {ps} (w : Walk L i ps q) : i≤q := by
  induction w with
  | nil => exact le_rfl
  | cons e _ ih => exact (feeds_later L e).le.trans ih

theorem column_later {H : Finset (Id Cir)} {a w : Id Cir}
    (good : a∈ThresholdSecondaryReceivers.good Cir n H) (inc : w∈effective L M a) : a<w := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp inc
  exact lt_of_lt_of_le (ThresholdSecondaryReceivers.receiver_later L good hr).1
    (walk_le M (trace_ok L M r).1)

include reg in
theorem outgoing_none (H : Finset (Id Cir)) (a w b : Id Cir)
    (good : a∈ThresholdSecondaryReceivers.good Cir n H) (inc : w∈effective L M a)
    (room : (missing L H a).card+(missing L H b).card+
        (exceptional L M H a).card<H.card) : active L w b≠true := by
  classical
  by_cases eq : a=b
  · subst b
    have lt := column_later M good inc
    have off := earlier_off L w (n+a.val) (Nat.add_lt_add_left lt n)
    intro on
    exact Bool.false_ne_true (off.symm.trans on)
  · obtain ⟨f,mem,ma,mb,warm⟩ := pivot H (missing L H a) (missing L H b)
      (exceptional L M H a) room
    apply outgoing_conflict M reg H a w b f eq inc mem warm
    · simpa [missing,mem] using ma
    · simpa [missing,mem] using mb


include reg in
theorem outside_high (H : Finset (Id Cir)) (a w : Id Cir)
    (good : a∈ThresholdSecondaryReceivers.good Cir n H) (inc : w∈effective L M a)
    (density : w∈H → (missing L H a).card+(exceptional L M H a).card<
      (H.filter (fun f => Edge L f w)).card) : w∉H := by
  intro mem
  have bound := Finset.card_le_card
    (neighbors_bad M reg H a w (column_later M good inc).ne inc)
  have cap := Finset.card_union_le (missing L H a) (exceptional L M H a)
  exact (Nat.not_lt_of_ge (bound.trans cap)) (density mem)

include reg in
/-- Quantify the second row using minimum degree two on the final, peeled
effective graph. Four finite exceptional sets suffice for all comparisons. -/
theorem final_column (H R : Finset (Id Cir)) (c w v : Id Cir)
    (cr : c∈R) (cv : effective L M c={w,v})
    (core : ThresholdColumnPeel.MinTwo (fun col r => col∈effective L M r) R)
    (good : c∈ThresholdSecondaryReceivers.good Cir n H)
    (room : ∀ b∈H,(missing L H c).card+(missing L H b).card+
        (exceptional L M H c).card<H.card) :
    ∃ a∈R,a≠c ∧ ∀ b∈H,
      b∉(missing L H a ∪ exceptional L M H a) ∪
        (missing L H c ∪ exceptional L M H c) →
      ¬Edge L b w ∧ active L w b≠true ∧ active L b w≠true := by
  classical
  have cw : w∈effective L M c := by simp [cv]
  obtain ⟨a,ar,ac,av⟩ := core c cr v (by simp [cv])
  refine ⟨a,ar,ac,?_⟩
  intro b hb clean
  have miss : b∉missing L H a ∧ b∉exceptional L M H a ∧
      b∉missing L H c ∧ b∉exceptional L M H c := by
    simp only [Finset.mem_union,not_or] at clean
    exact ⟨clean.1.1,clean.1.2,clean.2.1,clean.2.2⟩
  refine ⟨?_,outgoing_none M reg H c w b good cw (room b hb),?_⟩
  · intro edge
    have bad := neighbors_bad M reg H c w (column_later M good cw).ne cw
      (Finset.mem_filter.mpr ⟨hb,edge⟩)
    simp [miss.2.2.1,miss.2.2.2] at bad
  · intro probe
    have bad := incoming_bad M reg H a c w v ac cv av
      (Finset.mem_filter.mpr ⟨hb,probe⟩)
    simp [miss.1,miss.2.2.1,miss.2.1] at bad

end ThresholdColumnConflicts
