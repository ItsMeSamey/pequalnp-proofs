import Std

namespace CycleParity

abbrev Triple := Bool × Bool × Bool
def h (x : Triple) := x.1 ^^ (x.2.1 && x.2.2)
def flip (b : Bool) (x : Triple) : Triple := (x.1 ^^ b, x.2)
theorem flip_flip (b : Bool) (x : Triple) : flip b (flip b x) = x := by
  obtain ⟨a,c,d⟩ := x
  cases a <;> cases b <;> rfl
theorem h_flip (b : Bool) (x : Triple) : h (flip b x) = (h x ^^ b) := by
  obtain ⟨a,c,d⟩ := x
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

-- Number the vertices starting immediately after an omitted edge.
-- Edges 0,...,n-1 form the resulting path, and edge n closes the cycle.
def gauge (s t : Nat → Bool) : Nat → Bool
  | 0 => false
  | i+1 => (gauge s t i ^^ s i) ^^ t i

abbrev Input (n : Nat) := Fin (n+1) → Triple
def transport {n : Nat} (s t : Nat → Bool) (x : Input n) : Input n :=
  fun i => flip (gauge s t i.val) (x i)
theorem transport_twice {n : Nat} (s t : Nat → Bool) (x : Input n) :
    transport s t (transport s t x) = x := by
  funext i
  apply flip_flip

def edges {n : Nat} (s : Nat → Bool) (x : Input n) (i : Fin n) : Bool :=
  (h (x i.castSucc) ^^ h (x i.succ)) ^^ s i.val

theorem path_transport {n : Nat} (s t : Nat → Bool) (x : Input n) (i : Fin n) :
    edges t (transport s t x) i = edges s x i := by
  simp only [edges, transport, h_flip, Fin.val_castSucc, Fin.val_succ, gauge]
  generalize h (x i.castSucc) = a
  generalize h (x i.succ) = b
  generalize gauge s t i.val = c
  generalize s i.val = d
  generalize t i.val = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

-- An explicit involutive bijection between fibers of ANY observation on the path.
def fiberMap {n : Nat} (s t : Nat → Bool) (P : (Fin n → Bool) → Prop) :
    {x : Input n // P (edges s x)} → {x : Input n // P (edges t x)} :=
  fun x => ⟨transport s t x.val, by
    rw [show edges t (transport s t x.val) = edges s x.val from funext (path_transport s t x.val)]
    exact x.property⟩

def closed {n : Nat} (s : Nat → Bool) (x : Input n) : Bool :=
  (h (x (Fin.last n)) ^^ h (x 0)) ^^ s n

def parity (s : Nat → Bool) : Nat → Bool
  | 0 => false
  | i+1 => parity s i ^^ s i

theorem telescope {n : Nat} (s : Nat → Bool) (x : Input n)
    (z : ∀ i, edges s x i = false) (k : Nat) (hk : k ≤ n) :
    h (x ⟨k,by omega⟩) = (h (x 0) ^^ parity s k) := by
  induction k with
  | zero => simp [parity]
  | succ k ih =>
    have prev := ih (by omega)
    have next := z ⟨k,by omega⟩
    change ((h (x ⟨k,_⟩) ^^ h (x ⟨k+1,_⟩)) ^^ s k) = false at next
    rw [prev] at next
    simp only [parity]
    exact (by intro a b c d hh; bv_decide : ∀ a b c d : Bool, ((a ^^ b) ^^ c ^^ d) = false → c = (a ^^ (b ^^ d))) _ _ _ _ next

theorem closing_forced {n : Nat} (s : Nat → Bool) (x : Input n)
    (z : ∀ i, edges s x i = false) : closed s x = parity s (n+1) := by
  have last := telescope s x z n (Nat.le_refl n)
  unfold closed
  change h (x (Fin.last n)) = _ at last
  rw [last]
  simp only [parity]
  exact (by intro a b c; bv_decide : ∀ a b c : Bool, (((a ^^ b) ^^ a) ^^ c) = (b ^^ c)) _ _ _

theorem full_zero_iff {n : Nat} (s : Nat → Bool) :
    (∃ x : Input n, (∀ i, edges s x i = false) ∧ closed s x = false) ↔
      parity s (n+1) = false := by
  constructor
  · rintro ⟨x,hp,hc⟩
    exact (closing_forced s x hp).symm.trans hc
  · intro hp
    let x : Input n := transport (fun _ => false) s (fun _ => (false,false,false))
    have hz (i : Fin n) : edges s x i = false :=
      path_transport (fun _ => false) s (fun _ => (false,false,false)) i
    exact ⟨x,hz,(closing_forced s x hz).trans hp⟩

theorem gauge_comm (s t : Nat → Bool) (i : Nat) : gauge s t i = gauge t s i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [gauge, ih]
    bv_decide

theorem fiberMap_inverse {n : Nat} (s t : Nat → Bool) (P : (Fin n → Bool) → Prop)
    (x : {x : Input n // P (edges s x)}) :
    fiberMap t s P (fiberMap s t P x) = x := by
  apply Subtype.ext
  funext i
  change flip (gauge t s i.val) (flip (gauge s t i.val) (x.val i)) = x.val i
  rw [gauge_comm t s]
  apply flip_flip

end CycleParity
