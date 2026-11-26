import T2SoleOrSuffix
import T2CubeAgreement
namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RawIsolation

def reader (swap : Bool) (x p : Nat) : Gate := if swap then binary .or p x else binary .or x p

theorem reader_bit (swap : Bool) (x p : Nat) (w : List Bool) :
    val (reader swap x p) w=(w.getD x false || w.getD p false) := by
  cases swap <;> simp [reader,val,binary,gateOp,GateOp.eval,Bool.or_comm]

theorem prefix_zero (gs : List Gate) (k : Nat) (w : List Bool)
    (ok : SuffixOK k gs) (zero : ∀ i,w.getD i false=false) :
    ∀ i,(run gs w).getD i false=false := by
  induction gs generalizing w k with
  | nil => exact zero
  | cons g gs ih =>
    obtain ⟨⟨o,l,r,rfl,_,_⟩,tail⟩ := ok
    change ∀ i,(run gs (w++[val (binary o l r) w])).getD i false=false
    apply ih _ _ tail
    intro i
    have bit : val (binary o l r) w=false := by
      change val (Row.full (Row.mk o l r .both)) w = false
      rw [row_full]; change act o (w.getD l false) (w.getD r false) = false
      rw [zero l,zero r]; cases o <;> rfl
    by_cases hi : i<w.length
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi] using zero i
    · have past : w.length ≤ i := by omega
      simp only [bit,List.getD_eq_getElem?_getD,List.getElem?_append_right past]
      cases i-w.length <;> simp

theorem sole_clean (n : Nat) (x : Fin n) (p out : Nat) (pre post : List Gate) (swap : Bool)
    (distinct : p≠x.val) (notOut : out≠x.val) (ok : SuffixOK n pre)
    (computes : Computes n ⟨pre ++ reader swap x.val p :: post,out⟩)
    (left : ∀ g∈pre,x.val∉g.inputs) (right : ∀ g∈post,x.val∉g.inputs) :
    ∀ s : Finset (Fin n), s.card<2 → (run pre (vector s)).getD p false=false := by
  have z : ∀ i, (run pre (vector (∅ : Finset (Fin n)))).getD i false=false := by
    apply prefix_zero pre n _ ok
    intro i
    rw [vec_get]; split <;> simp
  intro s small
  by_cases empty : s=∅
  · subst s; exact z p
  have card : s.card=1 := by
    have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    omega
  obtain ⟨y,rfl⟩ := Finset.card_eq_one.mp card
  by_cases same : y=x
  · subst y
    have off := unread_run pre (off_insert (∅ : Finset (Fin n)) x) left
    simpa using (off.2 p distinct).symm.trans (z p)
  · let u := vector ({y} : Finset (Fin n))
    let v := vector (insert x ({y} : Finset (Fin n)))
    have off : AgreeOff x.val u v := off_insert {y} x
    have eqp := (unread_run pre off left).2 p distinct
    cases changed : (run pre u).getD p false with
    | false => rfl
    | true =>
      have other := eqp.symm.trans changed
      have eq := isolated_reader pre post (reader swap x.val p) off notOut left right
        (by simp only [reader_bit,changed,other,Bool.or_true])
      let C : Circuit := ⟨pre ++ reader swap x.val p :: post,out⟩
      change C.eval u = C.eval v at eq
      have yes : C.eval v=true := (computes _).mpr (by simp [Finset.card_insert_of_notMem,Ne.symm same])
      have no := (computes {y}).mp (eq.trans yes)
      simp at no
end T2SoleOrSplice
