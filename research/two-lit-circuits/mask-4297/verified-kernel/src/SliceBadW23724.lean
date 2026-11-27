import SliceConsequences
import MaskCode23724
import Numeric23724
namespace Probe23724
open ProbeFrontier

private theorem code_read {S : Finset (Mask (Fin 15))} {x : Mask (Fin 15)} (hx : x ∈ S) :
    encode x ∈ codes S := mem_codes.mpr ⟨x,hx,rfl⟩

private theorem pair_false {S : Finset (Mask (Fin 15))} {b t : ℕ}
    (sl : LiveSlice target b t S) (p n : ℕ) (mode : Bool) (noNot : mode = true → t=0)
    (h : Numeric23724.pairCut (codes S) p n mode = true) : False := by
  simp only [Numeric23724.pairCut, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hp,hn⟩,pt⟩,nt⟩,bits⟩ := h
  let pp : Fin 15 := ⟨p,hp⟩
  let nn : Fin 15 := ⟨n,hn⟩
  have pos : target pp = true := pt
  have neg : target nn = false := nt
  cases mode with
  | false =>
    obtain ⟨x,hx,diff⟩ := sl.asRun.separates pp nn (by simp [pos,neg])
    apply diff
    have eq := bits (encode x) (code_read hx)
    have same : (encode x).testBit p = (encode x).testBit n := by simpa using eq
    exact (encode_bit x pp).symm.trans (same.trans (encode_bit x nn))
  | true =>
    have bad := sl.monotone (noNot rfl) pp nn (by
      intro x hx
      have eq := bits (encode x) (code_read hx)
      change (!( (encode x).testBit p && !(encode x).testBit n)) = true at eq
      have ep : (encode x).testBit p = x pp := encode_bit x pp
      have en : (encode x).testBit n = x nn := encode_bit x nn
      rw [ep,en] at eq
      cases hi : x pp <;> cases hj : x nn <;> simp_all)
    rw [pos,neg] at bad
    exact (by decide : ¬(true ≤ false)) bad

private theorem sole_elim {S : Finset (Mask (Fin 15))} {a : Mask (Fin 15)}
    (p n : ℕ) (pol : Bool) (h : Numeric23724.sole (codes S) (encode a) p n pol = true) :
    ∃ pp nn : Fin 15, target pp = true ∧ target nn = false ∧ a pp = pol ∧ a nn = !pol ∧
      ∀ x ∈ S, x ≠ a → x pp = x nn := by
  simp only [Numeric23724.sole,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hp,hn⟩,pos⟩,neg⟩,ap⟩,an⟩,others⟩ := h
  let pp : Fin 15 := ⟨p,hp⟩
  let nn : Fin 15 := ⟨n,hn⟩
  refine ⟨pp,nn,pos,neg,(encode_bit a pp).symm.trans ap,(encode_bit a nn).symm.trans an,?_⟩
  intro x hx hne
  have hcode : encode x ≠ encode a := fun he => hne (encode_injective he)
  have eq := others (encode x) (code_read hx)
  have eq' : (encode x).testBit p = (encode x).testBit n := by simpa [hcode] using eq
  exact (encode_bit x pp).symm.trans (eq'.trans (encode_bit x nn))

private theorem tight_false {S : Finset (Mask (Fin 15))} {b t B : ℕ}
    (sl : LiveSlice target b t S) (hb : b ≤ B) (p n q m ix : ℕ)
    (h : (B+1 == (codes S).length && match (codes S)[ix]? with
      | none => false
      | some x => Numeric23724.sole (codes S) x p n true && Numeric23724.sole (codes S) x q m false) = true) : False := by
  rw [Bool.and_eq_true] at h
  have hlen : B+1 = S.card := by simpa only [beq_iff_eq,length_codes] using h.1
  have card := sl.card_le
  have orient := sl.unate (by omega)
  have right := h.2
  split at right
  · contradiction
  next x hx =>
    obtain ⟨a,ha,ea⟩ := mem_codes.mp (List.mem_of_getElem? hx)
    subst x
    rw [Bool.and_eq_true] at right
    rcases right with ⟨one,two⟩
    obtain ⟨i,j,hi,hj,ai,aj,rest1⟩ := sole_elim _ _ true one
    obtain ⟨k,l,hk,hl,ak,al,rest2⟩ := sole_elim _ _ false two
    exact orient.no_opposite k l i j hk hl hi hj ak al ai aj rest2 rest1

theorem slice_not_badW {S : Finset (Mask (Fin 15))} {b t B T : ℕ}
    (sl : LiveSlice target b t S) (hb : b ≤ B) (ht : t ≤ T) (w : ℕ) :
    Numeric23724.badW B T (codes S) w ≠ true := by
  intro h
  simp only [Numeric23724.badW] at h
  split at h
  · have wrong : B+1 < S.card := by simpa [length_codes] using h
    have := sl.card_le
    omega
  · exact pair_false sl _ _ false (by simp) h
  · rw [Bool.and_eq_true] at h
    rcases h with ⟨ht0,hpair⟩
    have : T = 0 := by simpa using ht0
    exact pair_false sl _ _ true (by omega) hpair
  · exact tight_false sl hb _ _ _ _ _ h
end Probe23724
