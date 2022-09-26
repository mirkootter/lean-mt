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
  validate : State -> Score -> Prop
  
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


end TaskM
