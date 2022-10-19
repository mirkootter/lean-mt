import Mt.Thread

namespace Mt

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

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

def iterate (s : System spec) : s.ThreadIndex -> System spec
  | thread_idx =>
    if (s.threads.get thread_idx).block_until s.state then 
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
    else
      s

theorem iterate_threads (s : System spec) (thread_idx : s.ThreadIndex)
  (blocked_until : (s.threads.get thread_idx).block_until s.state) :
  (s.iterate thread_idx).threads =
    match (s.threads.get thread_idx).iterate s.state with
      | Thread.IterationResult.Done .. => s.threads.eraseIdx thread_idx.val
      | Thread.IterationResult.Panic .. => s.threads.eraseIdx thread_idx.val
      | Thread.IterationResult.Running _ thread => s.threads.set thread_idx.val thread :=by
  rw [iterate]
  simp only [blocked_until, ite_true]
  cases h : Thread.iterate (List.get s.threads thread_idx) s.state <;> rfl

theorem iterate_panics (s : System spec) (thread_idx : s.ThreadIndex)
  (blocked_until : (s.threads.get thread_idx).block_until s.state) :
  (s.iterate thread_idx).panics =
    match (s.threads.get thread_idx).iterate s.state with
      | Thread.IterationResult.Done .. => s.panics
      | Thread.IterationResult.Panic .. => s.panics + 1
      | Thread.IterationResult.Running .. => s.panics :=by
  rw [iterate]
  simp only [blocked_until, ite_true]
  cases h : Thread.iterate (List.get s.threads thread_idx) s.state <;> rfl

inductive reduces_to : System spec -> System spec -> Prop where
| single {a b} (idx : a.ThreadIndex) (iteration : a.iterate idx = b) : reduces_to a b
| trans {a b c} (a_to_b : a.reduces_to b) (b_to_c : b.reduces_to c) : reduces_to a c

def reduces_to_or_eq (a b : System spec) : Prop :=a = b ∨ a.reduces_to b

theorem reduces_to_or_eq.refl (a : System spec) : a.reduces_to_or_eq a :=Or.inl rfl
theorem reduces_to_or_eq.trans {a b c : System spec} :
  a.reduces_to_or_eq b → b.reduces_to_or_eq c → a.reduces_to_or_eq c :=by
  intro ab bc
  cases ab <;> cases bc <;> rename_i h₁ h₂
  . rw [h₁, h₂] ; exact Or.inl rfl
  . rw [h₁] ; exact Or.inr h₂
  . rw [h₂.symm] ; exact Or.inr h₁
  . exact Or.inr <| h₁.trans h₂


end System

end Mt
