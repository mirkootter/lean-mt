import Mt.Task

namespace Mt

structure Thread (spec : Spec) where
  T : Type
  reservation : spec.Reservation
  task : TaskM spec T

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def mk_thread {T : Type} (task : TaskM spec T) : Thread spec := {
  T
  reservation := IsReservation.empty
  task }

namespace Thread

def valid (thread : Thread spec) : Prop :=
  thread.task.valid_for_reservation thread.reservation

inductive IterationResult (spec : Spec) where
  | Done : spec.State -> IterationResult spec
  | Panic : spec.State -> IterationResult spec
  | Running : spec.State -> Thread spec -> IterationResult spec

def IterationResult.state : IterationResult spec -> spec.State
  | Done state => state
  | Panic state => state
  | Running state _ => state

def iterate : Thread spec -> spec.State -> IterationResult spec
  | ⟨T, r, task⟩, state =>
    match task.iterate r state with
    | TaskM.IterationResult.Done _ state' _ => IterationResult.Done state'
    | TaskM.IterationResult.Panic _ state' _ => IterationResult.Panic state'
    | TaskM.IterationResult.Continuation reservation state' task => 
      IterationResult.Running state' { T, reservation, task }

end Thread

/-- Describes a system of zero or more threads running in parallel

  Systems can be iterated one atomic step at a time by choosing
  one of its threads. They keep track of the number of threads
  which panicked during execution
-/
structure System (spec : Spec) where
  state   : spec.State
  threads : List (Thread spec)
  panics  : Nat

namespace System

def ThreadIndex (s : System spec) : Type :=Fin s.threads.length
def done (s : System spec) : Bool :=s.threads.length = 0

protected def sum_reservations : List (Thread spec) -> spec.Reservation
  | [] => IsReservation.empty
  | thread :: threads => thread.reservation + System.sum_reservations threads

def reservations (s : System spec) : spec.Reservation :=
  System.sum_reservations s.threads

def other_reservations (s : System spec) (thread_idx : s.ThreadIndex) : spec.Reservation :=
  System.sum_reservations <| s.threads.eraseIdx thread_idx.val

theorem decompose_reservation (s : System spec) (thread_idx : s.ThreadIndex) :
  s.reservations = (s.other_reservations thread_idx) + (s.threads.get thread_idx).reservation :=by
  suffices
    ∀ (l : List <| Thread spec) (idx : Fin l.length),
    System.sum_reservations l = System.sum_reservations (l.eraseIdx idx.val) + (l.get idx).reservation from
    this s.threads thread_idx
  clear s thread_idx
  
  intro l
  induction l
  . intro idx
    have : idx.val < 0 :=idx.isLt
    contradiction
  . intro idx
    rename_i thread threads IH
    cases h : idx.val
    . have : idx = Fin.mk 0 (by simp_arith) :=Fin.eq_of_val_eq h
      simp only [this, List.get, List.eraseIdx, System.sum_reservations]
      exact IsReservation.toIsCommutative.comm _ _
    . rename_i n
      have idx_ok : n + 1 < (thread :: threads).length :=calc
        n + 1 = idx.val :=h.symm
        _ < _ :=idx.isLt
      have : idx = Fin.mk (n + 1) idx_ok :=Fin.eq_of_val_eq h
      simp only [this, List.get, List.eraseIdx, System.sum_reservations]
      clear this h idx
      rw [IsReservation.toIsAssociative.assoc]
      apply congrArg (thread.reservation + .)
      exact IH <| Fin.mk n (Nat.le_of_succ_le_succ idx_ok)

def iterate (s : System spec) : s.ThreadIndex -> System spec
  | thread_idx =>
    match (s.threads.get thread_idx).iterate s.state with
      | Thread.IterationResult.Done state =>
        {
          state
          threads := s.threads.eraseIdx thread_idx.val
          panics := s.panics
        }
      | Thread.IterationResult.Panic state =>
        {
          state
          threads := s.threads.eraseIdx thread_idx.val
          panics := s.panics + 1
        }
      | Thread.IterationResult.Running state thread =>
        {
          state
          threads := s.threads.set thread_idx.val thread
          panics := s.panics
        }

def reduces_single (a b : System spec) : Prop :=
  ∃ idx : a.ThreadIndex, a.iterate idx = b

def reduces_to : System spec -> System spec -> Prop :=TC reduces_single
def reduces_to_or_eq (a b : System spec) : Prop :=a = b ∨ a.reduces_to b

theorem reduces_to_or_eq.refl (a : System spec) : a.reduces_to_or_eq a :=Or.inl rfl
theorem reduces_to_or_eq.trans {a b c : System spec} :
  a.reduces_to_or_eq b → b.reduces_to_or_eq c → a.reduces_to_or_eq c :=by
  intro ab bc
  cases ab <;> cases bc <;> rename_i h₁ h₂
  . rw [h₁, h₂] ; exact Or.inl rfl
  . rw [h₁] ; exact Or.inr h₂
  . rw [h₂.symm] ; exact Or.inr h₁
  . exact Or.inr <| TC.trans a b c h₁ h₂

/-- Central validation predicate for reasoning about systems.

  A valid system has the following property: Given any future
  iteration of the system (or the system itself), the following
  holds:
  * No threads have panicked yet (and they never will)
  * The combination of state and thread reservations are valid
    according to the specification
-/
def valid (s : System spec) : Prop :=
  ∀ s' : System spec, s.reduces_to_or_eq s' →
  s'.panics = 0 ∧ spec.validate s.reservations s.state

theorem fundamental_validation_theorem (s : System spec)
  (no_panics_yet : s.panics = 0)
  (initial_valid : spec.validate s.reservations s.state)
  (threads_valid : ∀ idx : s.ThreadIndex, (s.threads.get idx).valid)
  : s.valid :=by
  sorry


end System

end Mt