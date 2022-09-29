import Mt.Reservation

-- Utils
theorem forall_ext {α : Type} {f g : α -> Prop}
  (h : ∀ a : α, f a = g a) : (∀ a : α, f a) = (∀ a : α, g a) :=by
  apply propext
  constructor <;> intro h' a
  . exact Eq.mp (h a) (h' a)
  . exact Eq.mpr (h a) (h' a)

namespace Mt

namespace impl

private inductive Step (spec : Spec) (T : Type) where
  | Done : spec.Reservation -> spec.State -> T -> Step spec T
  | Panic : spec.Reservation -> spec.State -> String -> Step spec T
  | Continuation : spec.Reservation -> spec.State -> (spec.Reservation -> spec.State -> Step spec T)
    -> Step spec T

private def Step.chain {spec : Spec} {U V : Type} :
  Step spec U -> (U -> spec.Reservation -> spec.State -> Step spec V) -> Step spec V
  | Done reservation state u, f => Continuation reservation state (f u)
  | Panic reservation state msg, _ => Panic reservation state msg
  | Continuation reservation state cont, f =>
    Continuation reservation state (fun reservation s => chain (cont reservation s) f)

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

private def Step.valid {T : Type} : Step spec T -> spec.Reservation -> Prop
  | Done reservation state _, env_reservation =>
    spec.validate (env_reservation + reservation) state
  | Panic .., _ => False
  | Continuation reservation state cont, env_reservation =>
    (spec.validate (env_reservation + reservation) state) ∧
    ∀ (state' : spec.State) (env_reservation' : spec.Reservation),
      (spec.validate
        (env_reservation' + reservation)
        state')
      → valid (cont reservation state') env_reservation'

end impl

/-- Represents a single task which can be iterated one atomic operation at a time -/
def TaskM (spec : Spec) (T : Type) : Type :=spec.Reservation -> spec.State -> impl.Step spec T

namespace TaskM
open impl

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def pure {T : Type} (t : T) : TaskM spec T :=fun reservation state => Step.Done reservation state t
def bind {U V : Type} (mu : TaskM spec U) (f : U -> TaskM spec V) : TaskM spec V :=
  fun reservation state => (mu reservation state).chain f

def panic {T : Type} (msg : String) : TaskM spec T :=
  fun reservation state => Step.Panic reservation state msg

def bind_assoc {U V W : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  (g : V -> TaskM spec W) :
  mu.bind (fun u => (f u).bind g) = (mu.bind f).bind g :=by
  simp only [bind]
  apply funext ; intro reservation0
  apply funext ; intro s0
  induction mu reservation0 s0 <;> try rfl
  rename_i cont IH 
  simp only [Step.chain]
  conv => lhs ; arg 3 ; intro reservation s ; rw [IH reservation s]

/-- The result of a single iteration of a `TaskM`. If the task is not completed
  after this iteration, the `IterationResult` contains a continuation
  
  `IterationResult` contains the following information:
  * The (potentially modified) state after the iteration
  * The (potentially modified) reservation after the iteration
  * Information about the task state (Running / Done / Panic)
  * Optionally a continuation, if the task is still running
 -/
inductive IterationResult (spec : Spec) (T : Type) where
  | Done : spec.Reservation -> spec.State -> T -> IterationResult spec T
  | Panic : spec.Reservation -> spec.State -> String -> IterationResult spec T
  | Continuation : spec.Reservation -> spec.State -> TaskM spec T -> IterationResult spec T

/-- state after the iteration -/
def IterationResult.state {T : Type} : IterationResult spec T -> spec.State
  | Done _ state _ => state
  | Panic _ state _ => state
  | Continuation _ state _ => state

/-- reservation after the iteration -/
def IterationResult.reservation {T : Type} : IterationResult spec T -> spec.Reservation
  | Done reservation .. => reservation
  | Panic reservation .. => reservation
  | Continuation reservation .. => reservation

private def _root_.Mt.impl.step_to_iteration_result {T : Type} :
  impl.Step spec T -> IterationResult spec T
    | impl.Step.Done reservation state t => IterationResult.Done reservation state t
    | impl.Step.Panic reservation state msg => IterationResult.Panic reservation state msg
    | impl.Step.Continuation reservation state cont => IterationResult.Continuation reservation state cont

instance : Monad (TaskM spec) where
  pure :=pure
  bind :=bind

/-- iterates a given `TaskM` one atomic step -/
def iterate {T : Type} (p : TaskM spec T) (reservation : spec.Reservation) (state : spec.State) :
  IterationResult spec T :=impl.step_to_iteration_result <| p reservation state

/-- Iterating a pure `TaskM` yields `IterationResult.Done` with the provided constant.
  Neither state nor reservation are modified. -/
theorem iterate_pure {T : Type} : ∀ (reservation : spec.Reservation) (state : spec.State) (t : T),
  (pure t).iterate reservation state = IterationResult.Done reservation state t :=by intros; rfl

/-- Iteration of `a >>= b` iterates `a`.

  If this does not panic, the result will contain a continuation:
  * As long as `a` is not done, future iteration will still iterate on `a`
  * As soon as `a` is done with result `u`, the next iteration will iterate on `b u`
-/
theorem iterate_bind {U V : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  : ∀ (reservation0 : spec.Reservation) (s0 : spec.State),
    (mu >>= f).iterate reservation0 s0 = match mu.iterate reservation0 s0 with
    | IterationResult.Done reservation1 s1 u => IterationResult.Continuation reservation1 s1 (f u)
    | IterationResult.Panic reservation1 s1 msg => IterationResult.Panic reservation1 s1 msg
    | IterationResult.Continuation reservation1 s1 cont =>
      IterationResult.Continuation reservation1 s1 (cont.bind f) :=by
    intro reservation0 s0
    simp only [Bind.bind, bind, iterate, impl.step_to_iteration_result]
    cases mu reservation0 s0 <;> rfl

/-- A thread is called valid for a given reservation if and only if it does not panic and
  respects the invariant `spec.validate` in this and all following iterations.
  
  During each iteration, the environment provides a reservation and a state. A valid thread
  is only required to enforce the invariant if the environment behaves correctly:
  * the environment must not change the reservation; the provided reservation has to be the exactly
    the reservation which was returned by the previous iteration of this thread
  * the environment must only provide valid combinations for state and reservation

  **Note** If there is no valid state given the current reservation, the environment cannot
    provide a matching state, i.e. the thread will not be called anymore. Hence,
    we call the thread valid in this case: Whatever it would do does not matter,
    it cannot break anything we want to reason about
  
  **Note** This definition uses internal implementation details and should not
    be unfolded. Use the `valid_for_reservation.def` theorem instead.
-/
def valid_for_reservation {T : Type} (task : TaskM spec T) (reservation : spec.Reservation) : Prop :=
  ∀ (state : spec.State) (env_r : spec.Reservation),
  spec.validate (env_r + reservation) state →
  impl.Step.valid (task reservation state) env_r

/-- Main theorem to justify the definition of `valid_for_reservation` -/
theorem valid_for_reservation.def {T : Type} (task : TaskM spec T) (reservation : spec.Reservation) :
  task.valid_for_reservation reservation =
    ∀ (state : spec.State) (env_r : spec.Reservation),
    spec.validate (env_r + reservation) state →
    match task.iterate reservation state with
      | IterationResult.Done reservation' state' _ => spec.validate (env_r + reservation') state'
      | IterationResult.Panic .. => False
      | IterationResult.Continuation reservation' state' cont =>
        (spec.validate (env_r + reservation') state') ∧
        cont.valid_for_reservation reservation' :=by
  simp only [iterate, Mt.impl.step_to_iteration_result, valid_for_reservation]
  apply forall_ext
  intro state
  cases task reservation state <;> simp only [Mt.impl.Step.valid]

end TaskM

end Mt