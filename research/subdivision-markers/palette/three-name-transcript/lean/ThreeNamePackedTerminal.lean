import ThreeNamePackedSteps2
import ThreeNameRejection
namespace ThreeNamePackedExample
open ThreeNamePacked ThreeNameChain ThreeNameSplitCircuit
open scoped BigOperators
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def incs (i : I) : BitVec 4 := ([12, 9, 10, 5, 3, 6, 0, 3, 0, 0, 0, 0, 0, 0, 12, 12, 9, 5] : List (BitVec 4)).getD i.val 0
def tails (i : I) : Fin 4 := ([3, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 2] : List (Fin 4)).getD i.val 0
def heads (i : I) : Fin 4 := ([2, 3, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0] : List (Fin 4)).getD i.val 0
def frows (i : Fin 4) : BitVec 7 := ([9, 1, 5, 13] : List (BitVec 7)).getD i.val 0
def rrows (i : Fin 7) : BitVec 4 := ([2, 0, 6, 12, 0, 0, 0] : List (BitVec 4)).getD i.val 0
/-- Each pair gives one input bit and its packed output image. -/
def sparseRun {w h : ℕ} : List (Fin w × BitVec h) → BitVec w → BitVec h
  | [], _ => 0
  | (j,image)::rest, x =>
    (if x.getLsbD j.val then image else 0) ^^^ sparseRun rest x

def sparseLinear {w h : ℕ} : List (Fin w × BitVec h) → Vec w →ₗ[ZMod 2] Vec h
  | [] => 0
  | (j,image)::rest => (LinearMap.proj j).smulRight (decode image) + sparseLinear rest

theorem sparse_decode {w h : ℕ} (ops : List (Fin w × BitVec h)) (x : BitVec w) :
    decode (sparseRun ops x) = sparseLinear ops (decode x) := by
  induction ops with
  | nil => exact decode_zero _
  | cons a rest ih =>
    obtain ⟨j,image⟩ := a
    rw [sparseRun,decode_xor,ih]
    change _ = (decode x j) • decode image + sparseLinear rest (decode x)
    have val : decode x j = (if x.getLsbD j.val then 1 else 0) := rfl
    rw [val]
    cases hb : x.getLsbD j.val <;> simp
    exact ThreeNamePacked.decode_zero h

theorem sparseSum {E : Type*} {w h : ℕ} (g : Finset E) (a : E → BitVec w)
    (b : E → BitVec h) (ops : List (Fin w × BitVec h))
    (ok : ∀ e ∈ g, sparseRun ops (a e) = b e) (s : Finset E) (sub : s ⊆ g) :
    sparseLinear ops (∑ i ∈ s, decode (a i)) = ∑ i ∈ s, decode (b i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sparse_decode,ok i (sub hi)]

theorem sparseKernel {E : Type*} {w h : ℕ} (g : Finset E) (a : E → BitVec w)
    (b : E → BitVec h) (forward : List (Fin w × BitVec h))
    (backward : List (Fin h × BitVec w))
    (hf : ∀ e ∈ g, sparseRun forward (a e) = b e)
    (hr : ∀ e ∈ g, sparseRun backward (b e) = a e)
    (s : Finset E) (sub : s ⊆ g) :
    (∑ i ∈ s, decode (a i)) = 0 ↔ (∑ i ∈ s, decode (b i)) = 0 := by
  constructor
  · intro hz
    rw [← sparseSum g a b forward hf s sub,hz,map_zero]
  · intro hz
    rw [← sparseSum g b a backward hr s sub,hz,map_zero]

def fops : List (Fin 7 × BitVec 4) := [(0, 15), (2, 12), (3, 9)]
def rops : List (Fin 4 × BitVec 7) := [(1, 5), (2, 12), (3, 8)]
theorem fchecked : ∀ e ∈ g3, sparseRun fops (words e) = incs e := by decide
theorem rchecked : ∀ e ∈ g3, sparseRun rops (incs e) = words e := by decide
/-- Check incidence in the packed basis, counting a loop's two equal ends modulo two. -/
def endpointCheck {E : Type} {w : Nat} (g : Finset E)
    (words : E → BitVec w) (l r : E → Fin w) : Bool :=
  decide (∀ e ∈ g, ∀ j : Fin w,
    (words e).getLsbD j.val = (decide (j = l e) ^^ decide (j = r e)))

theorem endpoint_bit_sound {E : Type} {w : Nat} (g : Finset E)
    (words : E → BitVec w) (l r : E → Fin w) (ok : endpointCheck g words l r = true) :
    ∀ e ∈ g, decode (words e) = ThreeNameIncidenceRank.incidence l r e := by
  unfold endpointCheck at ok
  intro e he
  funext j
  have bit := (of_decide_eq_true ok) e he j
  change (if (words e).getLsbD j.val then (1 : ZMod 2) else 0) =
    (if j = l e then 1 else 0) + (if j = r e then 1 else 0)
  rw [bit]
  have formula (p q : Prop) [Decidable p] [Decidable q] :
      (if (decide p ^^ decide q) then (1 : ZMod 2) else 0) =
      (if p then 1 else 0) + (if q then 1 else 0) := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide
  exact formula _ _

theorem incidenceWord : ∀ e ∈ g3, decode (incs e) = ThreeNameIncidenceRank.incidence tails heads e := endpoint_bit_sound g3 incs tails heads (by decide)
theorem terminalKernel (T : Finset I) (ht : T ⊆ g3) :
(∑ i ∈ T, decode (words i)) = 0 ↔ (∑ i ∈ T, ThreeNameIncidenceRank.incidence tails heads i) = 0 := by
  rw [← Finset.sum_congr rfl (fun i hi => incidenceWord i (ht hi))]
  exact sparseKernel g3 words incs fops rops fchecked rchecked T ht
theorem noRooted : ¬ Rooted p0 roots := by
  apply rejects (R := roots) (p := p0) (q := p3) (by exact ⟨0, by decide⟩) (fun v => by funext i; exact (show ∀ z : ZMod 2, z+z=0 by decide) (v i)) path
  rintro ⟨C,hg,hr,hc⟩
  have gc : Circuit (ThreeNameIncidenceRank.incidence tails heads) C :=
    ⟨hc.1,(terminalKernel C hg).mp hc.2.1,fun T ht hn z => hc.2.2 T ht hn ((terminalKernel T (ht.trans hg)).mpr z)⟩
  exact ThreeNameIncidenceRank.circuit_excludes_three tails heads C gc 3 0 1 2 (by decide) (by decide) (by decide) hr (by decide) (by decide) (by decide)
def ordinary (i : Fin 8) : BitVec 7 := ([4, 5, 16, 20, 24, 32, 36, 64] : List (BitVec 7)).getD i.val 0
def originalLabel (i : Fin 8) : I := ⟨i.val+6,by have := i.isLt; omega⟩
theorem original_positions : ∀ i, words (originalLabel i) = ordinary i ∧ originalLabel i ∈ g0 := by decide
/-- The three selectors index the eight entries of the packed root table. -/
def rootMaskWord (a b c : Bool) :=
  (if a then words 0 else 0) ^^^
    ((if b then words 1 else 0) ^^^ (if c then words 2 else 0))

private theorem decode_pick {w : Nat} (h : Prop) [Decidable h] (x : BitVec w) :
    decode (if decide h then x else 0) = if h then decode x else 0 := by
  by_cases ok : h <;> simp [ok]
  exact ThreeNamePacked.decode_zero w

theorem root_mask_sum (P : Finset I) (hp : P ⊆ roots) :
    (∑ i ∈ P, p0.col i) =
      decode (rootMaskWord (decide (0 ∈ P)) (decide (1 ∈ P)) (decide (2 ∈ P))) := by
  have filtered : roots.filter (fun i => i ∈ P) = P := by
    ext i
    exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨hp h,h⟩⟩
  have h0 : (0 : I) ∉ ({1,2} : Finset I) := by decide
  have h1 : (1 : I) ∉ ({2} : Finset I) := by decide
  calc
    _ = ∑ i ∈ roots.filter (fun i => i ∈ P), p0.col i := by rw [filtered]
    _ = _ := by
      rw [Finset.sum_filter]
      simp only [roots,Finset.sum_insert h0,Finset.sum_insert h1,Finset.sum_singleton,
        rootMaskWord,decode_xor,decode_pick,p0]

theorem root_independent : Independent p0.col roots := by
  have table : ∀ a b c : Bool, rootMaskWord a b c = 0 →
      a = false ∧ b = false ∧ c = false := by decide
  intro P hp hn hz
  rw [root_mask_sum P hp] at hz
  have word := decode_injective (hz.trans (decode_zero _).symm)
  obtain ⟨ha,hb,hc⟩ := table _ _ _ word
  obtain ⟨i,hi⟩ := hn
  have mem := hp hi
  simp only [roots,Finset.mem_insert,Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl
  · simpa [hi] using ha
  · simpa [hi] using hb
  · simpa [hi] using hc

theorem noPhysical (S : Finset I) (hg : S ⊆ g0) (dj : Disjoint roots S)
    (total : (∑ i ∈ S, p0.col i) = ∑ i ∈ roots, p0.col i)
    (trace : ∀ Q ⊆ S, ∀ P ⊆ roots, (∑ i ∈ Q, p0.col i) = (∑ i ∈ P, p0.col i) →
      (∑ i ∈ P, p0.col i) = 0 ∨ (∑ i ∈ P, p0.col i) = ∑ i ∈ roots, p0.col i) : False := by
  have rn : roots.Nonempty := ⟨0, by decide⟩
  have ind : Independent p0.col roots := root_independent
  have binary : ∀ v : Vec 7, v+v=0 := fun v => by funext i; exact (show ∀ z : ZMod 2, z+z=0 by decide) (v i)
  obtain ⟨C,hC,hr,hc⟩ := ThreeNameRootLift.from_trace p0.col roots S rn dj binary ind total trace
  exact noRooted ⟨C,hC.trans (Finset.union_subset (by decide : roots ⊆ g0) hg),hr,hc⟩
#print axioms noPhysical
#print axioms noRooted
end ThreeNamePackedExample
