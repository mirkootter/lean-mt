import Mt.Reservation
import Mt.Task.Impl

namespace Mt

/-- Monad to describe single threaded algorithms. Tasks can be iterated
  step by step until they finally complete or panic.

  `TaskM` is a monad, i.e. you can use the do-notation to write code:

  ```
  import Mt.Task.Basic
  open Mt

  abbrev spec : Spec :={
    State := Nat,
    Reservation := UnitReservation,
    validate :=λ _ _ => True
  }

  def sample_task : TaskM spec Bool :=do
    if (<- TaskM.atomic_read λ n => n) > 100 then
      -- reset to 100
      TaskM.atomic_read_modify λ _ => 100
      return false
    
    TaskM.atomic_assert λ n => n < 500
    
    TaskM.atomic_read_modify λ n => n + 7
    return true 
  ```

  Note: `TaskM` hat an associative bind operator, but it is not
  a lawful monad: Binding two `pure` cannot be simplified into
  a single pure, because it requires two iterations to complete.
-/
def TaskM (spec : Spec) (T : Type) : Type :=TaskM.impl.TaskM spec T

/-- The result of a single iteration of `TaskM`.

  Independent of the result, the resulting shared state after
  the iteration can be retrieved using `IterationResult.state`
-/
inductive TaskM.IterationResult (spec : Spec) (T : Type)
| Done : spec.State -> T -> IterationResult spec T
| Panic : spec.State -> String -> IterationResult spec T
| Running : spec.State -> (spec.State -> Bool) -> TaskM spec T -> IterationResult spec T

variable {spec : Spec}

def TaskM.IterationResult.state {T spec} : IterationResult spec T -> spec.State
| Done s _ => s
| Panic s _ => s
| Running s .. => s

instance TaskM.instMonad : Monad (TaskM spec) where
  pure :=impl.TaskM.pure
  bind :=impl.TaskM.bind

theorem TaskM.bind_assoc {U V W : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  (g : V -> TaskM spec W) :
  mu >>= (fun u => (f u) >>= g) = (mu >>= f) >>= g :=by
  simp only [Bind.bind]
  exact impl.TaskM.bind_assoc ..

/-- Atomic `TaskM` primitive with read/write-access to the shared state.

  Additional to performing a read-modify operation, it returns a value.

  Example: Compare Exchange (https://en.wikipedia.org/wiki/Compare-and-swap)
 -/
def TaskM.atomic_read_modify_read {T : Type}
  (f : spec.State -> T × spec.State)
  : TaskM spec T :=impl.TaskM.atomic_read_modify_read f

/-- Atomic `TaskM` primitive to perform read-modify operations on the
  shared state. It does not return anything. -/
def TaskM.atomic_read_modify
  (f : spec.State -> spec.State) : TaskM spec Unit :=
  atomic_read_modify_read λ s => ⟨⟨⟩, f s⟩

/-- Atomic `TaskM` primitive to perform read the shared state. It
  does not change anything -/
def TaskM.atomic_read {T : Type}
  (f : spec.State -> T)
  : TaskM spec T :=
  atomic_read_modify_read λ s => match f s with
    | t => ⟨t, s⟩

/-- Atomic `TaskM` primitive which throws an exception. The current thread
  panics and will be removed from the system -/
def TaskM.panic {T : Type} (msg : String) : TaskM spec T :=
  impl.TaskM.panic msg

/-- Atomic `TaskM` primitive to assert a given condition. The condition
  is checked atomically. If it returns `false`, the current thread panics. -/
def TaskM.atomic_assert
  (cond : spec.State -> Bool)
  : TaskM spec Unit :=impl.TaskM.atomic_assert cond

/-- `TaskM` primitive which blocks the current thread until a given
  condition holds, and executes a read-modify-read operation afterwards.
  
  There are neither spurious wakeups nor race conditions: The system will
  only perform the read-modify-read operation if the provided condition
  holds. If it does not, the thread will block. -/
def TaskM.atomic_blocking_rmr
  (block_until : spec.State -> Bool)
  (f : spec.State -> T × spec.State)
  : TaskM spec T :=impl.TaskM.atomic_blocking_rmr block_until f

/-- Iterate a given thread on a given state and provides an `IterationResult`.

  The task may complete or panic. If it is does not, it is still running
  and a continuation will be provided in the result -/
def TaskM.iterate {T : Type} : TaskM spec T ->
  spec.State -> IterationResult spec T :=
  λ p s => match p s with
  | impl.IterationResult.Done s' t => IterationResult.Done s' t
  | impl.IterationResult.Panic s' msg => IterationResult.Panic s' msg
  | impl.IterationResult.Running s' block_until cont =>
      IterationResult.Running s' block_until cont

/-- Iteration of `pure t` always completes with result `t` -/
theorem TaskM.iterate_pure {T : Type} :
  ∀ (s : spec.State) (t : T),
  iterate (pure t) s = IterationResult.Done s t :=by intros ; rfl

/-- Iteration of `a >>= f` iterates `a` and returns a continuation.

  * If the `a` iteration has completed with result `t`, the next
    iteration will start work on `f t`
  * If the `a` iteration has not completed yet, the next iteration
    will continue.
  * If `a` has panicked, the exception is propagated.
 -/
theorem TaskM.iterate_bind {U V : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  : ∀ (s : spec.State),
  iterate (mu >>= f) s = match iterate mu s with
    | IterationResult.Done s' u => IterationResult.Running s' (λ _ => true) (f u)
    | IterationResult.Panic s' msg => IterationResult.Panic s' msg
    | IterationResult.Running s' block_until cont =>
        IterationResult.Running s' block_until (cont >>= f) :=by
  intro s
  simp only [Bind.bind, iterate, impl.TaskM.bind]
  cases mu s <;> rfl

/-- Iteration of a read-modify-read-operation will perform the read modify
  and complete with the computed result. -/
theorem TaskM.iterate_rmr {T : Type}
  (f : spec.State -> T × spec.State)
  : ∀ s,
  iterate (atomic_read_modify_read f) s = match f s with
    | ⟨t, s'⟩ => IterationResult.Done s' t :=by intros ; rfl

/-- Iteration of a read-modify operation will perform the read modify
  operation and complete with `Unit.unit` -/
theorem TaskM.iterate_rm
  (f : spec.State -> spec.State)
  : ∀ s,
  iterate (atomic_read_modify f) s = match f s with
    | s' => IterationResult.Done s' ⟨⟩ :=by
  apply iterate_rmr

/-- Iteration of a read operation will compute a value based on the
  current shared state and complete with the result -/
theorem TaskM.iterate_read
  (f : spec.State -> T × spec.Reservation)
  : ∀ s,
  iterate (atomic_read f) s = match f s with
    | t => IterationResult.Done s t :=by
  apply iterate_rmr

/-- Iteration of a panic will fail -/
theorem TaskM.iterate_panic {T : Type} (msg : String)
  : ∀ (s : spec.State),
    iterate (panic (T :=T) msg) s = IterationResult.Panic s msg :=by
  intros ; rfl

/-- Iteration of an assertion will atomically check the condition
  and succeed or fail depending on the result. -/
theorem TaskM.iterate_assert
  (cond : spec.State -> Bool)
  : ∀ s,
  iterate (atomic_assert cond) s = if cond s then
    IterationResult.Done s ⟨⟩
  else
    IterationResult.Panic s "Assertion failed" :=by
  intro s
  simp only [atomic_assert, impl.TaskM.atomic_assert, iterate]
  cases cond s <;> simp only [ite_false, ite_true]

/-- Iteration of a `atomic_blocking_rmr` operation will always
  return a continuation.
  
  The `IterationResult` contains the blocking predicate and
  the desired read-modify-read operation. The caller should ensure
  that the read-modify-operation is only iterated when the blocking
  predicate holds. -/
theorem TaskM.iterate_blocking_rmr
  (block_until : spec.State -> Bool)
  (f : spec.State -> T × spec.State)
  : ∀ s,
  iterate (atomic_blocking_rmr block_until f) s = IterationResult.Running s
    block_until (atomic_read_modify_read f) :=by intros ; rfl

/-- Well founded relation on `TaskM` fulfilled by continuations with their parents.

  It can be used to perform well founded recursion `TaskM` without using the
  implementation details of `TaskM`. Whenever `TaskM.iterate` returns a
  continuation, the continuation will be *smaller* according to this
  relation.
  -/
inductive TaskM.is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {s s'}
    {block_until : spec.State -> Bool}
    (iteration : p.iterate s = IterationResult.Running s' block_until cont)
    : is_direct_cont cont p 

/-- See `TaskM.is_direct_cont` -/
theorem TaskM.is_direct_cont_wf {T : Type} :
  WellFounded (@is_direct_cont spec T) :=by
  constructor ; intro (p : impl.TaskM spec T)

  induction p using WellFounded.induction
  . exact impl.TaskM.is_direct_cont.wf
  . clear p ; rename_i p IH
    constructor ; intro cont is_cont
    apply IH
    cases is_cont
    rename_i s s' block_until iteration
    rw [iterate] at iteration
    cases h : p s <;> rw [h] at iteration <;> try contradiction
    injection iteration
    rename_i cont'_def ; rw [cont'_def] at h
    exact ⟨h⟩

instance TaskM.instWf {T : Type} :
  WellFoundedRelation (TaskM spec T) where
  rel :=is_direct_cont
  wf  :=is_direct_cont_wf

end Mt
