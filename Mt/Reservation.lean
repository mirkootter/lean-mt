import Mt.Utils.Nat

namespace Mt

/-- Class to represent 'reservations'

  Reservations are the main method for reasoning about inter-thread behaviour.
  
  Basic idea: Only threads with a certain reservation are allowed to do certain
  things. In many cases, some operation cannot be done atomically. Instead,
  a thread needs to do several steps. Using reservations, the thread can keep
  track about how many of those steps it has already accomplished. Other
  threads have no way to manipulate each other's reservation, only their own.

  For reasoning, the reservations of all threads have to be taken into account.
  However, we want:
  * The order of the other threads should not matter
  * It should not matter if there are 10 other threads, or only one which
    achieved those reservations
  
  As a consequence, we require an addition operator for reservations. Invariants
  used for reasoning may use both the shared state and the sum of all
  reservations, but not individual reservations. Each thread has to guarantee the
  invariant, but it only knows about its own reservation, i.e. it has a lower
  bound on the reservation, but nothing more. Therefore, it's actions are limited
  by the reservation it has already achieved on its own.

  ### Example:
  * There is one shared `Nat` variable `x`
  * Each thread performs the following three steps:
    - generate a random variable `n : Nat`
    - increase `x` by `n + 1` atomically
    - decrease `x` by `n` atomically
  * We want to reason that - in the end - `x` is never zero.

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
  threads with the same specification can be executed in parallel
-/
structure Spec where
  State : Type
  Reservation : Type
  [is_reservation : IsReservation Reservation]
  validate : Reservation -> State -> Prop

end Mt

namespace Mt
instance : IsReservation Nat where
  assoc     := Nat.add_assoc
  comm      := Nat.add_comm
  empty     := 0
  empty_add := Nat.zero_add

def LowerBound :=Nat

instance : Add LowerBound :=⟨Nat.max⟩

instance LowerBound.instance : IsReservation LowerBound where
  assoc :=Utils.Nat.max_assoc
  comm :=Utils.Nat.max_comm
  empty :=(0 : Nat)
  empty_add :=Utils.Nat.zero_max

structure UnitReservation

instance : IsReservation UnitReservation where
  add := λ _ _ => ⟨⟩
  assoc :=by intros ; rfl
  comm :=by intros ; rfl
  empty :=⟨⟩
  empty_add :=by intros ; rfl

inductive Lock (T : Type) where
| Unlocked
| Locked : T -> Lock T
| Invalid

def Lock.is_locked {T : Type} : Lock T -> Bool
| Locked _ => true
| _ => false

def Lock.is_locked_and_valid {T : Type} (valid : T -> Prop) : Lock T -> Prop
| Locked s => valid s
| _ => False

def Lock.is_unlocked {T : Type} : Lock T -> Bool
| Unlocked => true
| _ => false

def Lock.add {T : Type} : Lock T -> Lock T -> Lock T
| Unlocked, a => a
| a, Unlocked => a
| _, _ => Invalid

theorem Lock.eq_of_is_unlocked {T : Type} {r : Lock T} :
  r.is_unlocked → r = Lock.Unlocked :=by
  cases r
  . intros ; rfl
  . intros ; contradiction
  . intros ; contradiction

instance {T : Type} : Add (Lock T) :=⟨Lock.add⟩

theorem Lock.unlocked_add {T : Type} : ∀ a : Lock T, Unlocked + a = a :=by
  intro a ; cases a <;> rfl

theorem Lock.add_unlocked {T : Type} : ∀ a : Lock T, a + Unlocked = a :=by
  intro a ; cases a <;> rfl

theorem Lock.invalid_add {T : Type} : ∀ a : Lock T, Invalid + a = Invalid :=by
  intro a ; cases a <;> rfl

theorem Lock.add_comm {T : Type} : ∀ a b : Lock T, a + b = b + a :=by
  intro a b
  cases a <;> cases b <;> rfl

theorem Lock.add_assoc {T : Type} : ∀ a b c : Lock T,
  a + b + c = a + (b + c) :=by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl

instance {T : Type} : IsReservation (Lock T) where
  assoc :=Lock.add_assoc
  comm :=Lock.add_comm
  empty :=Lock.Unlocked
  empty_add :=Lock.unlocked_add

end Mt
