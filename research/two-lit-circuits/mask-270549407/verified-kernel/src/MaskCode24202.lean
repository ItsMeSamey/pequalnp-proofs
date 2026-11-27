import Probe24202
namespace Probe24202
open ProbeFrontier

def encode (x : Mask (Fin 21)) := Nat.ofBits x
def codes (S : Finset (Mask (Fin 21))) := (S.image encode).sort (· ≤ ·)
theorem encode_bit (x : Mask (Fin 21)) (i : Fin 21) : (encode x).testBit i.val = x i :=
  Nat.testBit_ofBits_lt _ _ _
theorem encode_high (x : Mask (Fin 21)) (i : ℕ) (h : 21 ≤ i) : (encode x).testBit i = false :=
  Nat.testBit_ofBits_ge _ _ h
theorem encode_lt (x : Mask (Fin 21)) : encode x < 2^21 :=
  Nat.lt_pow_two_of_testBit _ (encode_high x)
theorem encode_injective : Function.Injective encode := by
  intro a b h
  funext p; rw [←encode_bit a p, ←encode_bit b p, h]
theorem encode_sig (n : ℕ) (hn : n < 2^21) : encode (sig n) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases h : i<21
  · exact encode_bit (sig n) ⟨i,h⟩
  · rw [encode_high _ _ (by omega), Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (show 21 ≤ i by omega)))]
theorem encode_and (a b : Mask (Fin 21)) :
    encode (fun p => a p && b p) = encode a &&& encode b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  by_cases h : i<21
  · simp only [encode,Nat.testBit_ofBits_lt _ _ h]
  · simp [encode_high _ _ (show 21 ≤ i by omega)]
theorem encode_or (a b : Mask (Fin 21)) :
    encode (fun p => a p || b p) = encode a ||| encode b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  by_cases h : i<21
  · simp only [encode,Nat.testBit_ofBits_lt _ _ h]
  · simp [encode_high _ _ (show 21 ≤ i by omega)]
theorem encode_not (a : Mask (Fin 21)) :
    encode (fun p => !(a p)) = (2^21-1) ^^^ encode a := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor,Nat.testBit_two_pow_sub_one]
  by_cases h : i<21
  · simp [encode,Nat.testBit_ofBits_lt _ _ h,h]
  · simp [encode_high _ _ (show 21 ≤ i by omega),h]
theorem mem_codes {S : Finset (Mask (Fin 21))} {n : ℕ} :
    n ∈ codes S ↔ ∃ x ∈ S, encode x=n := by
  simp [codes]
theorem length_codes (S : Finset (Mask (Fin 21))) : (codes S).length=S.card := by
  simp [codes,Finset.card_image_of_injective S encode_injective]
theorem codes_start : codes start = [63,1986,30852,233736,860688,1721376] := by
  unfold codes start
  rw [Finset.image_image]
  have e : (encode ∘ raw) = fun i => rawCodes[i] := by
    funext i; apply encode_sig
    have h : ∀ j : Fin 6, rawCodes[j] < 2^21 := by decide +kernel
    exact h i
  rw [e]
  let l : List ℕ := [63,1986,30852,233736,860688,1721376]
  have eq : Finset.univ.image (fun i : Fin 6 => rawCodes[i]) = l.toFinset := by
    ext k
    simp only [Finset.mem_image,Finset.mem_univ,true_and,List.mem_toFinset]
    constructor
    · rintro ⟨i,rfl⟩
      exact (show ∀ j : Fin 6, rawCodes[j] ∈ l by decide +kernel) i
    · intro hk
      exact (show ∀ x ∈ l, ∃ j : Fin 6, rawCodes[j]=x by decide +kernel) k hk
  rw [eq]
  exact (List.toFinset_sort (· ≤ ·) (show l.Nodup by decide +kernel)).mpr (by decide +kernel)
theorem encode_target : encode target = 297183 := encode_sig _ (by decide)
theorem encode_zero : encode (zero : Mask (Fin 21)) = 0 := by decide +kernel
theorem encode_one : encode (one : Mask (Fin 21)) = 2^21-1 := by decide +kernel
private theorem codes_nodup (S : Finset (Mask (Fin 21))) : (codes S).Nodup :=
  Finset.sort_nodup _ _
private theorem codes_sorted (S : Finset (Mask (Fin 21))) : (codes S).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort _ _

private theorem codes_eq {S : Finset (Mask (Fin 21))} {l : List ℕ}
    (nd : l.Nodup) (sr : l.Pairwise (· ≤ ·))
    (mem : ∀ k, k ∈ l ↔ k ∈ S.image encode) : codes S = l := by
  have e : S.image encode = l.toFinset := by
    ext k; rw [List.mem_toFinset]; exact (mem k).symm
  unfold codes
  rw [e]; exact (List.toFinset_sort (· ≤ ·) nd).mpr sr

theorem codes_erase (S : Finset (Mask (Fin 21))) (a : Mask (Fin 21)) :
    codes (S.erase a) = (codes S).erase (encode a) := by
  apply codes_eq ((codes_nodup S).erase _) ((codes_sorted S).sublist (List.erase_sublist ..))
  intro k
  rw [(codes_nodup S).mem_erase_iff,mem_codes,Finset.mem_image]
  constructor
  · rintro ⟨hne,x,hx,rfl⟩
    exact ⟨x,Finset.mem_erase.mpr ⟨fun eq => hne (congrArg encode eq),hx⟩,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨ne,h⟩ := Finset.mem_erase.mp hx
    exact ⟨fun eq => ne (encode_injective eq),x,h,rfl⟩

theorem codes_insert {S : Finset (Mask (Fin 21))} {a : Mask (Fin 21)} (ha : a ∉ S) :
    codes (insert a S) = (encode a :: codes S).mergeSort := by
  have hx : encode a ∉ codes S := by
    rintro h
    obtain ⟨x,hx,eq⟩ := mem_codes.mp h
    exact ha (encode_injective eq ▸ hx)
  have perm := List.mergeSort_perm (encode a :: codes S) (· ≤ ·)
  apply codes_eq (perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hx,codes_nodup S⟩))
    (List.pairwise_mergeSort' (· ≤ ·) _)
  intro k
  rw [perm.mem_iff, List.mem_cons,mem_codes,Finset.image_insert,Finset.mem_insert,Finset.mem_image]
end Probe24202
