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
