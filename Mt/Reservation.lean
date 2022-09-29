-- utils
theorem nat_max_of_le {a b : Nat} : a ≤ b → a.max b = b :=by
  intro h ; simp only [Nat.max, h, ite_true]

theorem nat_max_of_eq' {a b : Nat} : a = b → a.max b = b :=
  λ h => nat_max_of_le (by rw [h] ; constructor)

theorem nat_max_of_eq {a b : Nat} : a = b → a.max b = a :=by
  intro h ; rw [nat_max_of_eq' h] ; exact h.symm

theorem nat_max_of_gt {a b : Nat} : a > b → a.max b = a :=by
  intro h ; simp only [Nat.max, Nat.not_le_of_gt h, ite_false]

theorem nat_max_of_ge {a b : Nat} : a ≥ b → a.max b = a :=by
  intro h
  cases Nat.eq_or_lt_of_le h <;> rename_i h
  . exact nat_max_of_eq h.symm
  . exact nat_max_of_gt h

theorem nat_max_of_lt {a b : Nat} : a < b → a.max b = b :=nat_max_of_le ∘ Nat.le_of_lt

theorem nat_max_comm  : ∀ a b : Nat, a.max b = b.max a :=by
  intro a b
  cases Nat.lt_or_ge a b <;> rename_i h
  . rw [nat_max_of_lt h, nat_max_of_gt h]
  cases Nat.eq_or_lt_of_le h <;> (clear h ; rename_i h)
  . rw [nat_max_of_eq h, nat_max_of_eq' h.symm]
  . rw [nat_max_of_lt h, nat_max_of_gt h]

theorem nat_max_assoc : ∀ a b c : Nat, (a.max b).max c = a.max (b.max c) :=by
  intros a b c
  cases Nat.lt_or_ge a b
  <;> cases Nat.lt_or_ge b c
  <;> rename_i ab bc
  . rw [nat_max_of_lt ab, nat_max_of_lt bc, nat_max_of_lt (trans ab bc)]
  . rw [nat_max_of_lt ab, nat_max_of_ge bc, nat_max_of_lt ab]
  . rw [nat_max_of_ge ab, nat_max_of_lt bc]
  . rw [nat_max_of_ge ab, nat_max_of_ge bc, nat_max_of_ge ab]
    exact nat_max_of_ge (trans bc ab : c ≤ a)

theorem nat_zero_max  : ∀ a : Nat, ((0 : Nat).max a) = a :=by
  intro a
  simp only [Nat.max, Nat.zero_le, ite_true]

namespace Mt

/-- Class to represent 'reservations'

  Reservations are the main method for reasoning about inter-thread behaviour.
  
  Basic idea: Only threads with a certain reservation are allowed to do certain
  things. In many cases, some operation cannot be done atomically. Instead,
  a thread needs to do several steps. Using reservations, the thread can keep
  track about how many of those steps he has already accomplished. Other
  threads have no way to manipulate each other's reservation, only their own.

  For reasoning, the reservations of all threads have to be taken into account.
  However, we want:
  * The order of the other threads should not matter
  * It should not matter if there are 10 other threads, or only one which
    achieved those reservations
  
  As a consequence, we require an addition operator for reservations. Invariants
  used for reasoning may use both the shared state and the sum of all
  reservations, but not individual reservations. Each thread has to guarantee the
  invariant, but it only knows about his own reservation, i.e. it has a lower
  bound on the reservation, but nothing more. Therefore, it's actions are limited
  by the reservation it has already achieved on its own.

  ### Example:
  * There is one shared `Nat` variable `x`
  * Each thread performs the following three steps:
    - generate a random variable `n : Nat`
    - increase `x` by `n + 1` atomically
    - decrease `x` by `n` atomically
  * We want to reason that - in the end - `x` is never zero
  Solution: We introduce a `reservation : Nat` reservation which keeps track of how much
  we have increased `x`. Therefore, the have the invariant ∑reservation = x.
  Now, we can easily reason about the thread:
  * Step 1: Generating the random number has no effect on the shared variable
  * Step 2: We increase `x` by `n + 1` and assign `reservation :=n + 1`. Since the
    reservations of the other threads have not changed, the invariant still holds
  * Step 3: Since no other thread can affect our reservation, we still know that
    `reservation = n + 1`. Because of our invariant, we also know
    `x = ∑reservation ≥ reservation = n + 1`. Therefore, we can safely decrease both `x`
    and `reservation` by `n` and we still have `x > 0`
  
  ### Sample instance
  ```
  instance : @Lean.IsAssociative Nat (.+.) :=⟨Nat.add_assoc⟩
  instance : @Lean.IsCommutative Nat (.+.) :=⟨Nat.add_comm⟩

  instance a : IsReservation Nat :=⟨0, Nat.zero_add⟩
  ```
-/
class IsReservation (T : Type)
  extends
    Add T,
    Lean.IsAssociative (@HAdd.hAdd T T T _),
    Lean.IsCommutative (@HAdd.hAdd T T T _)
  where
    empty : T
    empty_add : ∀ t : T, empty + t = t

/-- Specification for a multithreading system

  This specification specifies the context for threads but not the
  threads itself. Threads encode a specification in their type. Only
  threads with the same specification can be exected in parallel
-/
structure Spec where
  State : Type
  Reservation : Type
  [is_reservation : IsReservation Reservation]
  validate : Reservation -> State -> Prop
  reservations_can_be_dropped : -- if a thread drops its reservation, it should not break the system
    ∀ (r r' : Reservation) (state : State), validate (r + r') state → validate r state

end Mt

namespace Mt
  instance : IsReservation Nat where
    assoc     := Nat.add_assoc
    comm      := Nat.add_comm
    empty     := 0
    empty_add := Nat.zero_add

  def LowerBound :=Nat

  instance : Add LowerBound :=⟨Nat.max⟩

  instance : IsReservation LowerBound where
    assoc :=nat_max_assoc
    comm :=nat_max_comm
    empty :=(0 : Nat)
    empty_add :=nat_zero_max

end Mt
