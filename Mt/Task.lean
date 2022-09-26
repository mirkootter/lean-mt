-- Utils
theorem forall_ext {α : Type} {f g : α -> Prop}
  (h : ∀ a : α, f a = g a) : (∀ a : α, f a) = (∀ a : α, g a) :=by
  apply propext
  constructor <;> intro h' a
  . exact Eq.mp (h a) (h' a)
  . exact Eq.mpr (h a) (h' a)

namespace Mt


/-- Class to represent 'scores'

  Scores are the main method for reasoning about inter-thread behaviour.
  
  Basic idea: Only threads with a certain score are allowed to do certain
  things. In many cases, some operation cannot be done atomically. Instead,
  a thread needs to do several steps. Using scores, the thread can keep
  track about how many of those steps he has already accomplished. Other
  threads have no way to manipulate each other's score, only their own.

  For reasoning, the scores of all threads have to be taken into account.
  However, we want:
  * The order of the other threads should not matter
  * It should not matter if there are 10 other threads, or only one which
    achieved those scores
  
  As a consequence, we require an addition operator for scores. Invariants
  used for reasoning may use both the shared state and the sum of all
  scores, but not individual scores. Each thread has to guarantee the
  invariant, but it only knows about his own score, i.e. it has a lower
  bound on the score, but nothing more. Therefore, it's actions are limited
  by the score it has already achieved on its own.

  ### Example:
  * There is one shared `Nat` variable `x`
  * Each thread performs the following three steps:
    - generate a random variable `n : Nat`
    - increase `x` by `n + 1` atomically
    - decrease `x` by `n` atomically
  * We want to reason that - in the end - `x` is never zero
  Solution: We introduce a `score : Nat` score which keeps track of how much
  we have increased `x`. Therefore, the have the invariant ∑score = x.
  Now, we can easily reason about the thread:
  * Step 1: Generating the random number has no effect on the shared variable
  * Step 2: We increase `x` by `n + 1` and assign `score :=n + 1`. Since the
    scores of the other threads have not changed, the invariant still holds
  * Step 3: Since no other thread can affect our score, we still know that
    `score = n + 1`. Because of our invariant, we also know
    `x = ∑score ≥ score = n + 1`. Therefore, we can safely decrease both `x`
    and `score` by `n` and we still have `x > 0`
  
  ### Sample instance
  ```
  instance : @Lean.IsAssociative Nat (.+.) :=⟨Nat.add_assoc⟩
  instance : @Lean.IsCommutative Nat (.+.) :=⟨Nat.add_comm⟩

  instance a : IsScore Nat :=⟨0, Nat.zero_add⟩
  ```
-/
class IsScore (T : Type)
  extends
    Add T,
    Lean.IsAssociative (@HAdd.hAdd T T T _),
    Lean.IsCommutative (@HAdd.hAdd T T T _)
  where
    empty : T
    empty_add : ∀ t : T, empty + t = t


structure Spec where
  State : Type
  Score : Type
  [is_score : IsScore Score]
  validate : Score -> State -> Prop
  
namespace impl
private inductive Step (spec : Spec) (T : Type) where
  | Done : spec.Score -> spec.State -> T -> Step spec T
  | Panic : spec.Score -> spec.State -> String -> Step spec T
  | Continuation : spec.Score -> spec.State -> (spec.Score -> spec.State -> Step spec T) -> Step spec T

private def Step.chain {spec : Spec} {U V : Type} :
  Step spec U -> (U -> spec.Score -> spec.State -> Step spec V) -> Step spec V
  | Done score state u, f => Continuation score state (f u)
  | Panic score state msg, _ => Panic score state msg
  | Continuation score state cont, f => Continuation score state (fun score s => chain (cont score s) f)

private def Step.valid {T : Type} : Step spec T -> Prop
  | Done score state _ => spec.validate score state
  | Panic .. => False
  | Continuation score state cont =>
    (spec.validate score state) ∧ ∀ state' : spec.State, spec.validate score state' → valid (cont score state')

end impl

/-- Represents a single task which can be iterated one atomic operation at a time -/
def TaskM (spec : Spec) (T : Type) : Type :=spec.Score -> spec.State -> impl.Step spec T

namespace TaskM
open impl

variable {spec : Spec}

def pure {T : Type} (t : T) : TaskM spec T :=fun score state => Step.Done score state t
def bind {U V : Type} (mu : TaskM spec U) (f : U -> TaskM spec V) : TaskM spec V :=
  fun score state => (mu score state).chain f

def panic {T : Type} (msg : String) : TaskM spec T :=
  fun score state => Step.Panic score state msg

def bind_assoc {U V W : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  (g : V -> TaskM spec W) :
  mu.bind (fun u => (f u).bind g) = (mu.bind f).bind g :=by
  simp only [bind]
  apply funext ; intro score0
  apply funext ; intro s0
  induction mu score0 s0 <;> try rfl
  rename_i cont IH 
  simp only [Step.chain]
  conv => lhs ; arg 3 ; intro score s ; rw [IH score s]

/-- The result of a single iteration of a `TaskM`. If the task is not completed
  after this iteration, the `IterationResult` contains a continuation
  
  `IterationResult` contains the following information:
  * The (potentially modified) state after the iteration
  * The (potentially modified) score after the iteration
  * Information about the task state (Running / Done / Panic)
  * Optionally a continuation, if the task is still running
 -/
inductive IterationResult (spec : Spec) (T : Type) where
  | Done : spec.Score -> spec.State -> T -> IterationResult spec T
  | Panic : spec.Score -> spec.State -> String -> IterationResult spec T
  | Continuation : spec.Score -> spec.State -> TaskM spec T -> IterationResult spec T

/-- state after the iteration -/
def IterationResult.state {T : Type} : IterationResult spec T -> spec.State
  | Done _ state _ => state
  | Panic _ state _ => state
  | Continuation _ state _ => state

/-- score after the iteration -/
def IterationResult.score {T : Type} : IterationResult spec T -> spec.Score
  | Done score .. => score
  | Panic score .. => score
  | Continuation score .. => score

private def _root_.Mt.impl.step_to_iteration_result {T : Type} :
  impl.Step spec T -> IterationResult spec T
    | impl.Step.Done score state t => IterationResult.Done score state t
    | impl.Step.Panic score state msg => IterationResult.Panic score state msg
    | impl.Step.Continuation score state cont => IterationResult.Continuation score state cont

instance : Monad (TaskM spec) where
  pure :=pure
  bind :=bind

/-- iterates a given `TaskM` one atomic step -/
def iterate {T : Type} (p : TaskM spec T) (score : spec.Score) (state : spec.State) :
  IterationResult spec T :=impl.step_to_iteration_result <| p score state

/-- Iterating a pure `TaskM` yields `IterationResult.Done` with the provided constant.
  Neither state nor score are modified. -/
theorem iterate_pure {T : Type} : ∀ (score : spec.Score) (state : spec.State) (t : T),
  (pure t).iterate score state = IterationResult.Done score state t :=by intros; rfl

/-- Iteration of `a >>= b` iterates `a`.

  If this does not panic, the result will contain a continuation:
  * As long as `a` is not done, future iteration will still iterate on `a`
  * As soon as `a` is done with result `u`, the next iteration will iterate on `b u`
-/
theorem iterate_bind {U V : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  : ∀ (score0 : spec.Score) (s0 : spec.State),
    (mu >>= f).iterate score0 s0 = match mu.iterate score0 s0 with
    | IterationResult.Done score1 s1 u => IterationResult.Continuation score1 s1 (f u)
    | IterationResult.Panic score1 s1 msg => IterationResult.Panic score1 s1 msg
    | IterationResult.Continuation score1 s1 cont =>
      IterationResult.Continuation score1 s1 (cont.bind f) :=by
    intro score0 s0
    simp only [Bind.bind, bind, iterate, impl.step_to_iteration_result]
    cases mu score0 s0 <;> rfl

/-- A thread is called valid for a given score if and only if it does not panic and
  respects the invariant `spec.validate` in this and all following iterations.
  
  During each iteration, the environment provides a score and a state. A valid thread
  is only required to enforce the invariant if the environment behaves correctly:
  * the environment must not change the score; the provided score has to be the exactly
    the score which was returned by the previous iteration of this thread
  * the environment must only provide valid combinations for state and score

  **Note** If there is no valid state given the current score, the environment cannot
    provide a matching state, i.e. the thread will not be called anymore. Hence,
    we call the thread valid in this case: Whatever it would do does not matter,
    it cannot break anything we want to reason about
  
  **Note** This definition uses internal implementation details and should not
    be unfolded. Use the `valid_for_score.def` theorem instead.
-/
def valid_for_score {T : Type} (task : TaskM spec T) (score : spec.Score) : Prop :=
  ∀ state : spec.State, spec.validate score state →
  impl.Step.valid (task score state)

/-- Main theorem to justify the definition of `valid_for_score` -/
theorem valid_for_score.def {T : Type} (task : TaskM spec T) (score : spec.Score) :
  task.valid_for_score score =
    ∀ state : spec.State, spec.validate score state → 
    match task.iterate score state with
      | IterationResult.Done score' state' _ => spec.validate score' state'
      | IterationResult.Panic .. => False
      | IterationResult.Continuation score' state' cont =>
        (spec.validate score' state') ∧ cont.valid_for_score score' :=by
  simp only [iterate, Mt.impl.step_to_iteration_result, valid_for_score]
  apply forall_ext
  intro state
  cases task score state <;> simp only [Mt.impl.Step.valid]

end TaskM

end Mt